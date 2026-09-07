import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition45TwoEndsStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ExternalCoveringNumberIsometry

/-!
# Helpers for the two Lemma 8.13 applications in Proposition 8.9

These lemmas isolate the graph symmetry, subset inheritance, and monotonicity
used when applying the fixed strip-localization theorem in both endpoint
orders.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The historical stronger Alternative A implies the paper-facing union
alternative. -/
lemma WZ1Proposition8_9AlternativeA.toUnion
    {delta epsilon : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    (h : WZ1Proposition8_9AlternativeA
      delta epsilon F G₁ G₂) :
    WZ1Proposition8_9AlternativeAUnion
      delta epsilon F G₁ G₂ := by
  rcases h with
    ⟨base, direction, hdirection, hF, hG₁, _hG₂⟩
  exact ⟨base, direction, hdirection, hF, Or.inl hG₁⟩

/-- After specializing `G₁ = G₂`, the union alternative recovers the
historical two-endpoint conclusion used by the original Theorem 22. -/
lemma WZ1Proposition8_9AlternativeAUnion.same_endpoint
    {delta epsilon : ℝ}
    {F G : DiscreteSet 2}
    (h :
      WZ1Proposition8_9AlternativeAUnion
        delta epsilon F G G) :
    WZ1Proposition8_9AlternativeA
      delta epsilon F G G := by
  rcases h with
    ⟨base, direction, hdirection, hF, hG⟩
  rcases hG with hG | hG
  · exact ⟨base, direction, hdirection, hF, hG, hG⟩
  · exact ⟨base, direction, hdirection, hF, hG, hG⟩

/-- The paper-facing union alternative is monotone in the loss exponent. -/
lemma WZ1Proposition8_9AlternativeAUnion.mono_epsilon
    {delta epsilon₁ epsilon₂ : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    (h :
      WZ1Proposition8_9AlternativeAUnion
        delta epsilon₁ F G₁ G₂)
    (hepsilon : epsilon₁ ≤ epsilon₂)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    WZ1Proposition8_9AlternativeAUnion
      delta epsilon₂ F G₁ G₂ := by
  rcases h with
    ⟨base, direction, hdirection, hF, hEndpoint⟩
  have hpower :
      Kakeya.realRpowENN delta (epsilon₂ - 1) ≤
        Kakeya.realRpowENN delta (epsilon₁ - 1) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith))
  refine
    ⟨base, direction, hdirection, hpower.trans hF, ?_⟩
  rcases hEndpoint with hG₁ | hG₂
  · exact Or.inl (hpower.trans hG₁)
  · exact Or.inr (hpower.trans hG₂)

/-- The paper-facing union alternative is monotone under enlarging all three
vertex classes. -/
lemma WZ1Proposition8_9AlternativeAUnion.mono
    {delta epsilon : ℝ}
    {F F' G₁ G₁' G₂ G₂' : DiscreteSet 2}
    (h :
      WZ1Proposition8_9AlternativeAUnion
        delta epsilon F' G₁' G₂')
    (hF : F' ⊆ F)
    (hG₁ : G₁' ⊆ G₁)
    (hG₂ : G₂' ⊆ G₂) :
    WZ1Proposition8_9AlternativeAUnion
      delta epsilon F G₁ G₂ := by
  rcases h with
    ⟨base, direction, hdirection, hFCount, hEndpoint⟩
  have hFMono :
      wz1DiscreteLineCount F' 0 (wz1Perp2 direction) delta ≤
        wz1DiscreteLineCount F 0 (wz1Perp2 direction) delta := by
    simp [wz1DiscreteLineCount]
    gcongr
  refine
    ⟨base, direction, hdirection,
      hFCount.trans hFMono, ?_⟩
  rcases hEndpoint with hG₁Count | hG₂Count
  · left
    exact hG₁Count.trans (by
      simp [wz1DiscreteLineCount]
      gcongr)
  · right
    exact hG₂Count.trans (by
      simp [wz1DiscreteLineCount]
      gcongr)

/-- The selected `zeta` is strictly below the working Frostman loss. -/
lemma WZ1Proposition8_9Parameters.zeta_lt_workingLambda
    {epsilon : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hepsilonOne : epsilon < 1) :
    parameters.zeta < parameters.workingLambda := by
  calc
    parameters.zeta
        ≤ epsilon * parameters.workingLambda / 30 :=
      parameters.zeta_le_epsilon_workingLambda
    _ < parameters.workingLambda := by
      have hworking := parameters.workingLambda_pos
      nlinarith

/-- Alternative A for a stronger loss also gives Alternative A for every
larger requested loss. -/
lemma WZ1Proposition8_9AlternativeA.mono_epsilon
    {delta epsilon₁ epsilon₂ : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    (h :
      WZ1Proposition8_9AlternativeA
        delta epsilon₁ F G₁ G₂)
    (hepsilon : epsilon₁ ≤ epsilon₂)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    WZ1Proposition8_9AlternativeA
      delta epsilon₂ F G₁ G₂ := by
  rcases h with
    ⟨base, direction, hdirection, hF, hG₁, hG₂⟩
  have hpower :
      Kakeya.realRpowENN delta (epsilon₂ - 1) ≤
        Kakeya.realRpowENN delta (epsilon₁ - 1) := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith))
  exact
    ⟨base, direction, hdirection,
      hpower.trans hF,
      hpower.trans hG₁,
      hpower.trans hG₂⟩

/-- The long-projection alternative is monotone in its losses and graph. -/
lemma WZ1StripLocalizationLongProjection.mono
    {delta epsilon₁ eta₁ epsilon₂ eta₂ : ℝ}
    {H₁ H₂ : Finset (Point2 × Point2 × Point2)}
    (h : WZ1StripLocalizationLongProjection
      delta epsilon₁ eta₁ H₁)
    (hepsilon : epsilon₁ ≤ epsilon₂)
    (heta : eta₂ ≤ eta₁)
    (hgraph : H₁ ⊆ H₂)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (heta₁ : 0 < eta₁) :
    WZ1StripLocalizationLongProjection
      delta epsilon₂ eta₂ H₂ := by
  rcases h with
    ⟨rho, center, radius, hrhoLower, hrhoUpper,
      hradius, hlength, hcover⟩
  have hrho : 0 < rho := hdelta.trans_le hrhoLower
  let ratio := 2 * radius / rho
  have hnegativePower :
      1 ≤ Real.rpow delta (-eta₁) := by
    exact
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by linarith)
  have hratio : 1 ≤ ratio := by
    rw [show ratio = 2 * radius / rho by rfl,
      one_le_div hrho]
    calc
      rho = 1 * rho := by ring
      _ ≤ Real.rpow delta (-eta₁) * rho := by gcongr
      _ ≤ 2 * radius := hlength
  have hlength' :
      Real.rpow delta (-eta₂) * rho ≤ 2 * radius := by
    have hpower :
        Real.rpow delta (-eta₂) ≤
          Real.rpow delta (-eta₁) :=
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)
    exact
      (mul_le_mul_of_nonneg_right hpower hrho.le).trans hlength
  let dot : (Point2 × Point2 × Point2) → ℝ :=
    fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2)
  have hdot :
      wz1DotDifferenceSet H₁ ⊆
        wz1DotDifferenceSet H₂ := by
    intro value hvalue
    have hvalue₁ : value ∈ H₁.image dot := by
      exact_mod_cast hvalue
    have hvalue₂ : value ∈ H₂.image dot :=
      Finset.image_mono dot hgraph hvalue₁
    exact_mod_cast hvalue₂
  have hintersection :
      wz1DotDifferenceSet H₁ ∩
          Metric.closedBall center radius ⊆
        wz1DotDifferenceSet H₂ ∩
          Metric.closedBall center radius :=
    Set.inter_subset_inter hdot (Set.Subset.refl _)
  have hcoverMonotone :
      (Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H₁ ∩
            Metric.closedBall center radius) : ENNReal) ≤
        Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H₂ ∩
            Metric.closedBall center radius) := by
    exact_mod_cast
      Metric.externalCoveringNumber_mono_set hintersection
  have hpower :
      Kakeya.realRpowENN ratio (1 - epsilon₂) ≤
        Kakeya.realRpowENN ratio (1 - epsilon₁) := by
    exact ENNReal.ofReal_mono
      (Real.rpow_le_rpow_of_exponent_le
        hratio (by linarith))
  exact
    ⟨rho, center, radius, hrhoLower, hrhoUpper,
      hradius, hlength',
      hpower.trans (hcover.trans hcoverMonotone)⟩

/-- A scalar level strip is the corresponding affine line neighborhood. -/
lemma wz1LineNeighborhood_eq_strip
    {normal : Point2} (hnormal : ‖normal‖ = 1)
    {level width : ℝ} :
    {point : Point2 |
      |inner ℝ point normal - level| ≤ width} =
      wz1LineNeighborhood
        (level • normal) (wz1Perp2 normal) width := by
  have hperp :
      wz1Perp2 (wz1Perp2 normal) = -normal := by
    ext index
    fin_cases index <;>
      simp [wz1Perp2, EuclideanSpace.single]
  have hbase :
      inner ℝ (level • normal) normal = level := by
    rw [real_inner_smul_left,
      real_inner_self_eq_norm_sq, hnormal]
    norm_num
  ext point
  simp only [wz1LineNeighborhood, Set.mem_setOf_eq]
  have hinner :
      inner ℝ (point - level • normal)
          (wz1Perp2 (wz1Perp2 normal)) =
        -(inner ℝ point normal - level) := by
    rw [hperp, inner_neg_right, inner_sub_left, hbase]
  rw [hinner, abs_neg]

/-- The quarter-turn map preserves the Euclidean norm. -/
lemma wz1Perp2_norm (vector : Point2) :
    ‖wz1Perp2 vector‖ = ‖vector‖ := by
  have hcoordinates := wz1Perp2_coords vector
  have hsquare :
      ‖wz1Perp2 vector‖ ^ 2 = ‖vector‖ ^ 2 := by
    rw [norm2_sq (wz1Perp2 vector), norm2_sq vector,
      hcoordinates.1, hcoordinates.2]
    ring
  nlinarith [norm_nonneg (wz1Perp2 vector), norm_nonneg vector]

/-- Standard separation is inherited by coordinatewise subsets. -/
lemma WZ1StandardSeparation.mono
    {F G₁ G₂ F' G₁' G₂' : DiscreteSet 2}
    (h : WZ1StandardSeparation F G₁ G₂)
    (hF : F' ⊆ F) (hG₁ : G₁' ⊆ G₁)
    (hG₂ : G₂' ⊆ G₂) :
    WZ1StandardSeparation F' G₁' G₂' := by
  rcases h with
    ⟨hFdiameter, hG₁diameter, hG₂diameter,
      hmutual, horigin⟩
  exact
    ⟨fun first hfirst second hsecond =>
        hFdiameter first (hF hfirst) second (hF hsecond),
      fun first hfirst second hsecond =>
        hG₁diameter first (hG₁ hfirst) second (hG₁ hsecond),
      fun first hfirst second hsecond =>
        hG₂diameter first (hG₂ hfirst) second (hG₂ hsecond),
      fun first hfirst second hsecond =>
        hmutual first (hG₁ hfirst) second (hG₂ hsecond),
      fun point hpoint => horigin point (hF hpoint)⟩

/-- Swap the two endpoint coordinates of a tripartite edge. -/
def wz1SwapTriple
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (edge.1, edge.2.2, edge.2.1)

/-- Swap indices `1` and `2`. -/
def wz1SwapFin3 : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1

lemma wz1SwapFin3_involutive :
    Function.Involutive wz1SwapFin3 := by
  intro index
  fin_cases index <;> simp [wz1SwapFin3]

lemma wz1SwapFin3_injective :
    Function.Injective wz1SwapFin3 :=
  wz1SwapFin3_involutive.injective

/-- Encoding commutes with swapping the endpoint coordinates. -/
lemma wz1EncodeTriples_swap
    {H : Finset (Point2 × Point2 × Point2)} :
    wz1EncodeTriples (H.image wz1SwapTriple) =
      (wz1EncodeTriples H).image
        (fun edge index => edge (wz1SwapFin3 index)) := by
  ext encoded
  simp only [wz1EncodeTriples, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨source, hsource, rfl⟩, rfl⟩
    refine
      ⟨wz1TripleCoordinate source,
        ⟨source, hsource, rfl⟩, ?_⟩
    ext index
    fin_cases index <;>
      simp [wz1TripleCoordinate, wz1SwapTriple, wz1SwapFin3]
  · rintro
      ⟨encodedSource, ⟨source, hsource, rfl⟩, rfl⟩
    refine
      ⟨wz1SwapTriple source,
        ⟨source, hsource, rfl⟩, ?_⟩
    ext index
    fin_cases index <;>
      simp [wz1TripleCoordinate, wz1SwapTriple, wz1SwapFin3]

/-- Swapping the endpoint classes preserves uniform triple density. -/
lemma WZ1UniformTripleDensity.swap
    {density : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (h : WZ1UniformTripleDensity density F G₁ G₂ H) :
    WZ1UniformTripleDensity density
      F G₂ G₁ (H.image wz1SwapTriple) := by
  rcases h with
    ⟨hH, hsupport, hfibers⟩
  let swapFunction :
      (Fin 3 → Point2) → (Fin 3 → Point2) :=
    fun edge index => edge (wz1SwapFin3 index)
  have hswapInjective :
      Function.Injective swapFunction := by
    intro first second heq
    funext index
    have hcoordinate :=
      congrFun heq (wz1SwapFin3 index)
    simpa [swapFunction,
      wz1SwapFin3_involutive index] using hcoordinate
  let classes := wz1TripleVertexClasses F G₁ G₂
  let swappedClasses := wz1TripleVertexClasses F G₂ G₁
  have hclasses :
      ∀ index,
        swappedClasses index =
          classes (wz1SwapFin3 index) := by
    intro index
    fin_cases index <;>
      rfl
  have hencoded :
      wz1EncodeTriples (H.image wz1SwapTriple) =
        (wz1EncodeTriples H).image swapFunction := by
    exact wz1EncodeTriples_swap
  refine ⟨Finset.Nonempty.image hH _, ?_⟩
  rw [hencoded]
  refine ⟨?_, ?_⟩
  · intro edge hedge index
    rcases Finset.mem_image.mp hedge with
      ⟨source, hsource, rfl⟩
    change
      source (wz1SwapFin3 index) ∈
        swappedClasses index
    rw [hclasses index]
    exact hsupport source hsource (wz1SwapFin3 index)
  · intro edge hedge coordinates
    rcases Finset.mem_image.mp hedge with
      ⟨source, hsource, rfl⟩
    let swappedCoordinates :=
      coordinates.image wz1SwapFin3
    have hfiber :
        wz1HypergraphFiber
            ((wz1EncodeTriples H).image swapFunction)
            coordinates (swapFunction source) =
          (wz1HypergraphFiber
            (wz1EncodeTriples H)
            swappedCoordinates source).image swapFunction := by
      ext candidate
      simp only [wz1HypergraphFiber,
        Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨preimage, hpreimage, rfl⟩, hagree⟩
        refine ⟨preimage, ⟨hpreimage, ?_⟩, rfl⟩
        intro index hindex
        rcases Finset.mem_image.mp hindex with
          ⟨sourceIndex, hsourceIndex, rfl⟩
        exact hagree sourceIndex hsourceIndex
      · rintro ⟨preimage, ⟨hpreimage, hagree⟩, rfl⟩
        refine ⟨⟨preimage, hpreimage, rfl⟩, ?_⟩
        intro index hindex
        exact hagree
          (wz1SwapFin3 index)
          (Finset.mem_image_of_mem _ hindex)
    have hcard :
        ((wz1HypergraphFiber
          ((wz1EncodeTriples H).image swapFunction)
          coordinates (swapFunction source)).card : ENNReal) =
          (wz1HypergraphFiber
            (wz1EncodeTriples H)
            swappedCoordinates source).card := by
      rw [hfiber,
        Finset.card_image_of_injective _ hswapInjective]
    have huniv :
        (Finset.univ : Finset (Fin 3)).image wz1SwapFin3 =
          Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro index
      simpa [wz1SwapFin3_involutive index] using
        Finset.mem_image_of_mem wz1SwapFin3
          (Finset.mem_univ (wz1SwapFin3 index))
    have hcomplement :
        (Finset.univ \ coordinates).image wz1SwapFin3 =
          Finset.univ \ swappedCoordinates := by
      rw [Finset.image_sdiff _ _ wz1SwapFin3_injective,
        huniv]
    have hproduct :
        wz1VertexCardProduct swappedClasses
            (Finset.univ \ coordinates) =
          wz1VertexCardProduct classes
            (Finset.univ \ swappedCoordinates) := by
      have hfirst :
          wz1VertexCardProduct swappedClasses
              (Finset.univ \ coordinates) =
            ∏ index ∈ Finset.univ \ coordinates,
              ((classes (wz1SwapFin3 index)).card : ENNReal) := by
        simp [wz1VertexCardProduct, hclasses]
      rw [hfirst]
      let cardinality : Fin 3 → ENNReal :=
        fun index => (classes index).card
      have himage :
          (∏ index ∈ Finset.univ \ coordinates,
              cardinality (wz1SwapFin3 index)) =
            ∏ index ∈
                (Finset.univ \ coordinates).image wz1SwapFin3,
              cardinality index :=
        (Finset.prod_image
          (f := cardinality)
          (g := wz1SwapFin3)
          (s := Finset.univ \ coordinates)
          (Set.injOn_of_injective
            wz1SwapFin3_injective)).symm
      rw [himage, hcomplement]
      rfl
    rw [hcard, hproduct]
    exact hfibers source hsource swappedCoordinates

/-- A raw strip bound may be weakened by enlarging its coefficient. -/
lemma WZ1RawStripNonconcentration.weaken
    {delta zeta width : ℝ}
    {set : DiscreteSet 2} {constant : ENNReal}
    (h : WZ1RawStripNonconcentration
      delta zeta width set)
    (hconstant : (1 : ENNReal) ≤ constant) :
    WZ1WeightedRawStripNonconcentration
      delta zeta width constant set := by
  intro normal hnormal level radius hradius
  have hraw := h normal hnormal level radius hradius
  let factor :=
    ENNReal.ofReal
      ((Real.rpow width zeta)⁻¹ *
        Real.rpow radius zeta)
  calc
    ((set.filter fun point =>
      |inner ℝ point normal - level| ≤ radius).card : ENNReal)
        ≤ factor * set.enncard := hraw
    _ ≤ constant * factor * set.enncard := by
      have hfactor :
          factor ≤ constant * factor := by
        calc
          factor = 1 * factor := by simp
          _ ≤ constant * factor := by gcongr
      exact mul_le_mul_left hfactor set.enncard

/-- Swapping the endpoint coordinates negates the dot-difference set. -/
lemma wz1DotDifferenceSet_swap
    {H : Finset (Point2 × Point2 × Point2)} :
    wz1DotDifferenceSet (H.image wz1SwapTriple) =
      Neg.neg '' wz1DotDifferenceSet H := by
  ext value
  simp only [wz1DotDifferenceSet, Set.mem_image,
    Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨edge, ⟨source, hsource, rfl⟩, rfl⟩
    refine
      ⟨inner ℝ source.1
          (source.2.1 - source.2.2),
        ⟨source, hsource, rfl⟩, ?_⟩
    have hneg :
        inner ℝ source.1
            (source.2.2 - source.2.1) =
          -inner ℝ source.1
            (source.2.1 - source.2.2) := by
      rw [show source.2.2 - source.2.1 =
        -(source.2.1 - source.2.2) by abel]
      rw [inner_neg_right]
    simpa [wz1SwapTriple] using hneg.symm
  · rintro ⟨sourceValue, ⟨source, hsource, rfl⟩, rfl⟩
    refine
      ⟨wz1SwapTriple source,
        ⟨source, hsource, rfl⟩, ?_⟩
    have hneg :
        inner ℝ source.1
            (source.2.2 - source.2.1) =
          -inner ℝ source.1
            (source.2.1 - source.2.2) := by
      rw [show source.2.2 - source.2.1 =
        -(source.2.1 - source.2.2) by abel]
      rw [inner_neg_right]
    simpa [wz1SwapTriple] using hneg

/--
The long-projection conclusion is invariant under swapping the two endpoint
coordinates.
-/
lemma WZ1StripLocalizationLongProjection.swap
    {delta epsilon eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (h :
      WZ1StripLocalizationLongProjection
        delta epsilon eta (H.image wz1SwapTriple)) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  rcases h with
    ⟨rho, center, radius, hrhoLower, hrhoUpper,
      hradius, hlength, hcover⟩
  have hdot :
      wz1DotDifferenceSet H =
        Neg.neg ''
          wz1DotDifferenceSet (H.image wz1SwapTriple) := by
    rw [wz1DotDifferenceSet_swap]
    have hdoubleNeg :
        Neg.neg '' (Neg.neg '' wz1DotDifferenceSet H) =
          wz1DotDifferenceSet H := by
      ext value
      simp
    exact hdoubleNeg.symm
  have hball :
      Metric.closedBall (-center) radius =
        Neg.neg '' Metric.closedBall center radius := by
    ext value
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hnegInjective :
      Function.Injective (Neg.neg : ℝ → ℝ) := by
    intro first second heq
    simpa using heq
  have hintersection :
      wz1DotDifferenceSet H ∩
          Metric.closedBall (-center) radius =
        Neg.neg ''
          (wz1DotDifferenceSet
              (H.image wz1SwapTriple) ∩
            Metric.closedBall center radius) := by
    rw [hdot, hball, Set.image_inter hnegInjective]
  have hnegSurjective :
      Function.Surjective (Neg.neg : ℝ → ℝ) := by
    intro value
    exact ⟨-value, by ring⟩
  have hcoverEq :
      (Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall (-center) radius) : ENNReal) =
        (Metric.externalCoveringNumber
          (Real.toNNReal rho)
          (wz1DotDifferenceSet
              (H.image wz1SwapTriple) ∩
            Metric.closedBall center radius) : ENNReal) := by
    rw [hintersection]
    exact_mod_cast
      Isometry.externalCoveringNumber_image
        isometry_neg hnegSurjective
  exact
    ⟨rho, -center, radius, hrhoLower, hrhoUpper,
      hradius, hlength, by
        rw [hcoverEq]
        exact hcover⟩

/--
Transfer raw strip nonconcentration to a retained subset, paying the explicit
reciprocal retention loss.
-/
lemma WZ1RawStripNonconcentration.transfer_subset
    {delta zeta width : ℝ}
    {selected ambient : DiscreteSet 2}
    {retentionInv : ENNReal}
    (h :
      WZ1RawStripNonconcentration
        delta zeta width ambient)
    (hselected : selected ⊆ ambient)
    (hretention :
      ambient.enncard ≤
        retentionInv * selected.enncard) :
    WZ1WeightedRawStripNonconcentration
      delta zeta width retentionInv selected := by
  intro normal hnormal level radius hradius
  have hfilter :
      selected.filter
          (fun point =>
            |inner ℝ point normal - level| ≤ radius) ⊆
        ambient.filter
          (fun point =>
            |inner ℝ point normal - level| ≤ radius) :=
    Finset.filter_subset_filter _ hselected
  have hcard :
      ((selected.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
          ENNReal) ≤
        ((ambient.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card :
            ENNReal) := by
    exact_mod_cast Finset.card_le_card hfilter
  have hambient :=
    h normal hnormal level radius hradius
  calc
    ((selected.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
          ENNReal)
        ≤
          ((ambient.filter fun point =>
            |inner ℝ point normal - level| ≤ radius).card :
              ENNReal) := hcard
    _ ≤
        ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          ambient.enncard := hambient
    _ ≤
        ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          (retentionInv * selected.enncard) := by
      gcongr
    _ =
        retentionInv *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          selected.enncard := by
      ring

/--
Transfer weighted strip nonconcentration to a retained subset, multiplying
the old coefficient by the reciprocal retention loss.
-/
lemma WZ1WeightedRawStripNonconcentration.transfer_subset
    {delta zeta width : ℝ}
    {selected ambient : DiscreteSet 2}
    {constant retentionInv : ENNReal}
    (h :
      WZ1WeightedRawStripNonconcentration
        delta zeta width constant ambient)
    (hselected : selected ⊆ ambient)
    (hretention :
      ambient.enncard ≤
        retentionInv * selected.enncard) :
    WZ1WeightedRawStripNonconcentration
      delta zeta width (constant * retentionInv) selected := by
  intro normal hnormal level radius hradius
  have hfilter :
      selected.filter
          (fun point =>
            |inner ℝ point normal - level| ≤ radius) ⊆
        ambient.filter
          (fun point =>
            |inner ℝ point normal - level| ≤ radius) :=
    Finset.filter_subset_filter _ hselected
  have hcard :
      ((selected.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
          ENNReal) ≤
        ((ambient.filter fun point =>
          |inner ℝ point normal - level| ≤ radius).card :
            ENNReal) := by
    exact_mod_cast Finset.card_le_card hfilter
  have hambient :=
    h normal hnormal level radius hradius
  calc
    ((selected.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
          ENNReal)
        ≤
          ((ambient.filter fun point =>
            |inner ℝ point normal - level| ≤ radius).card :
              ENNReal) := hcard
    _ ≤
        constant *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          ambient.enncard := hambient
    _ ≤
        constant *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          (retentionInv * selected.enncard) := by
      gcongr
    _ =
        (constant * retentionInv) *
          ENNReal.ofReal
            ((Real.rpow width zeta)⁻¹ *
              Real.rpow radius zeta) *
          selected.enncard := by
      ring

/-- Enlarge the coefficient in a weighted raw strip estimate. -/
lemma WZ1WeightedRawStripNonconcentration.weaken
    {delta zeta width : ℝ}
    {constant constant' : ENNReal}
    {set : DiscreteSet 2}
    (h :
      WZ1WeightedRawStripNonconcentration
        delta zeta width constant set)
    (hconstant : constant ≤ constant') :
    WZ1WeightedRawStripNonconcentration
      delta zeta width constant' set := by
  intro normal hnormal level radius hradius
  have hbound :=
    h normal hnormal level radius hradius
  exact hbound.trans (by gcongr)

end Kakeya.Assouad
