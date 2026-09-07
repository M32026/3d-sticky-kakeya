import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanEnergy
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveWidthGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.StripGeometry
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Direct outside-strip covering core for WZ1 Lemma 49

This module contains the finite packing argument used when one graph-active
first-coordinate vertex escapes the enlarged orthogonal strip.  Unlike the
retired monolithic proof, the strip-width hypothesis is imposed only on the
actual dense second-coordinate fiber of the graph.  Unused ambient vertices
of `G₁` play no role.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/--
A `2 * rho`-separated finite real set needs at least its cardinality many
radius-`rho` balls.
-/
lemma wz1Lemma49_separated_real_covering_lower_bound
    {values : Finset ℝ} {rho : ℝ} (hrho : 0 < rho)
    (hseparated :
      ∀ first ∈ values, ∀ second ∈ values,
        first ≠ second → 2 * rho < |first - second|) :
    (values.card : ENNReal) ≤
      Metric.externalCoveringNumber
        (Real.toNNReal rho) (values : Set ℝ) := by
  let epsilon : NNReal := Real.toNNReal rho
  have hrhoNonneg : 0 ≤ rho := hrho.le
  have hepsilon : (epsilon : ℝ) = rho := by
    simp [epsilon, Real.toNNReal_of_nonneg hrhoNonneg]
  have hmetric :
      Metric.IsSeparated (2 * epsilon) (values : Set ℝ) := by
    rw [Metric.isSeparated_iff_setRelIsSeparated]
    intro first hfirst second hsecond hne
    have hvalue :=
      hseparated first hfirst second hsecond hne
    have hedist :
        edist first second =
          ENNReal.ofReal |first - second| := by
      simp [edist_dist, Real.dist_eq]
    have hcoe :
        (2 * epsilon : ENNReal) =
          ENNReal.ofReal (2 * rho) := by
      symm
      calc
        ENNReal.ofReal (2 * rho) =
            ENNReal.ofReal (2 * (epsilon : ℝ)) := by
          rw [hepsilon]
        _ = ENNReal.ofReal 2 *
              ENNReal.ofReal (epsilon : ℝ) :=
          ENNReal.ofReal_mul (by norm_num)
        _ = (2 * epsilon : ENNReal) := by simp
    change ¬edist first second ≤ (2 * epsilon : ENNReal)
    apply not_le.mpr
    rw [hcoe, hedist]
    exact
      (ENNReal.ofReal_lt_ofReal_iff
        (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr hvalue
  have hpacking :
      (values : Set ℝ).encard ≤
        Metric.packingNumber (2 * epsilon) (values : Set ℝ) :=
    hmetric.encard_le_packingNumber (Set.Subset.refl _)
  have hcover :
      Metric.packingNumber (2 * epsilon) (values : Set ℝ) ≤
        Metric.externalCoveringNumber epsilon (values : Set ℝ) :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber
      epsilon (values : Set ℝ)
  have hcard :
      (values.card : ENat) =
        (values : Set ℝ).encard := by
    exact (Set.encard_coe_eq_coe_finsetCard values).symm
  exact_mod_cast hcard ▸ hpacking.trans hcover

/--
Uniform tripartite density gives a dense `G₁` fiber after fixing one active
first-coordinate vertex and one active third-coordinate vertex.
-/
lemma wz1Lemma49_uniform_density_fiber_g1
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    (hDensity : WZ1UniformTripleDensity density F G₁ G₂ H)
    {first : Point2} (hfirst : first ∈ F)
    (hactive : ∃ edge ∈ H, edge.1 = first) :
    ∃ third : Point2, third ∈ G₂ ∧
      density * (G₁.card : ENNReal) ≤
        ((G₁.filter fun second =>
          (first, second, third) ∈ H).card : ENNReal) := by
  classical
  rcases hactive with ⟨sourceEdge, hsourceEdge, hsourceFirst⟩
  let second := sourceEdge.2.1
  let third := sourceEdge.2.2
  have hsourceEdgeEq :
      sourceEdge = (first, second, third) := by
    rcases sourceEdge with ⟨sourceFirst, sourceSecond, sourceThird⟩
    simp only [Prod.fst] at hsourceFirst
    subst sourceFirst
    rfl
  let encodedH := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  let encodedEdge : Fin 3 → Point2 :=
    wz1TripleCoordinate (first, second, third)
  have hencodedEdge : encodedEdge ∈ encodedH := by
    rw [hsourceEdgeEq] at hsourceEdge
    exact Finset.mem_image.mpr
      ⟨(first, second, third), hsourceEdge, rfl⟩
  let fixed : Finset (Fin 3) := {0, 2}
  have hfiber :
      density *
          wz1VertexCardProduct classes (Finset.univ \ fixed) ≤
        ((wz1HypergraphFiber encodedH fixed encodedEdge).card :
          ENNReal) :=
    hDensity.2.2 encodedEdge hencodedEdge fixed
  have hcomplement :
      (Finset.univ \ fixed : Finset (Fin 3)) = {1} := by
    decide
  have hproduct :
      wz1VertexCardProduct classes ({1} : Finset (Fin 3)) =
        (G₁.card : ENNReal) := by
    simp [wz1VertexCardProduct, classes,
      wz1TripleVertexClasses]
  rw [hcomplement, hproduct] at hfiber
  let fiber :=
    wz1HypergraphFiber encodedH fixed encodedEdge
  let projection : (Fin 3 → Point2) → Point2 :=
    fun edge => edge 1
  have hprojectionInjective :
      Set.InjOn projection (fiber : Set (Fin 3 → Point2)) := by
    intro edge hedge other hother heq
    have hedgeFixed :
        ∀ i ∈ fixed, edge i = encodedEdge i :=
      (Finset.mem_filter.mp hedge).2
    have hotherFixed :
        ∀ i ∈ fixed, other i = encodedEdge i :=
      (Finset.mem_filter.mp hother).2
    apply funext
    intro i
    fin_cases i
    · exact (hedgeFixed 0 (by decide)).trans
        (hotherFixed 0 (by decide)).symm
    · exact heq
    · exact (hedgeFixed 2 (by decide)).trans
        (hotherFixed 2 (by decide)).symm
  have hprojectionCard :
      (fiber.image projection).card = fiber.card :=
    Finset.card_image_of_injOn hprojectionInjective
  have hprojectionEq :
      fiber.image projection =
        G₁.filter fun candidate =>
          (first, candidate, third) ∈ H := by
    ext candidate
    constructor
    · intro hcandidate
      rcases Finset.mem_image.mp hcandidate with
        ⟨edge, hedge, hedgeCandidate⟩
      have hedgeEncoded : edge ∈ encodedH :=
        (Finset.mem_filter.mp hedge).1
      have hedgeFixed :
          ∀ i ∈ fixed, edge i = encodedEdge i :=
        (Finset.mem_filter.mp hedge).2
      rcases Finset.mem_image.mp hedgeEncoded with
        ⟨source, hsource, hsourceEncoded⟩
      have hsourceFirst :
          source.1 = first := by
        calc
          source.1 = edge 0 := congrFun hsourceEncoded 0
          _ = encodedEdge 0 := hedgeFixed 0 (by decide)
          _ = first := rfl
      have hsourceSecond :
          source.2.1 = candidate := by
        calc
          source.2.1 = edge 1 := congrFun hsourceEncoded 1
          _ = projection edge := rfl
          _ = candidate := hedgeCandidate
      have hsourceThird :
          source.2.2 = third := by
        calc
          source.2.2 = edge 2 := congrFun hsourceEncoded 2
          _ = encodedEdge 2 := hedgeFixed 2 (by decide)
          _ = third := rfl
      have hcandidateG₁ : candidate ∈ G₁ := by
        have hsupported :=
          hDensity.2.1 edge hedgeEncoded 1
        rw [← hedgeCandidate]
        simpa [projection, classes,
          wz1TripleVertexClasses] using hsupported
      have hsourceTuple :
          source = (first, candidate, third) := by
        exact Prod.ext hsourceFirst
          (Prod.ext hsourceSecond hsourceThird)
      exact Finset.mem_filter.mpr
        ⟨hcandidateG₁, by
          rw [hsourceTuple] at hsource
          exact hsource⟩
    · intro hcandidate
      have hcandidateG₁ := (Finset.mem_filter.mp hcandidate).1
      have hedge :=
        (Finset.mem_filter.mp hcandidate).2
      let edge : Fin 3 → Point2 :=
        wz1TripleCoordinate (first, candidate, third)
      have hedgeEncoded : edge ∈ encodedH :=
        Finset.mem_image.mpr
          ⟨(first, candidate, third), hedge, rfl⟩
      have hedgeFixed :
          ∀ i ∈ fixed, edge i = encodedEdge i := by
        intro i hi
        fin_cases i
        · rfl
        · simp [fixed] at hi
        · rfl
      exact Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨hedgeEncoded, hedgeFixed⟩,
          rfl⟩
  have hthirdG₂ : third ∈ G₂ := by
    have h := hDensity.2.1 encodedEdge hencodedEdge 2
    change encodedEdge 2 ∈ G₂ at h
    change third ∈ G₂ at h
    exact h
  refine ⟨third, hthirdG₂, ?_⟩
  rw [← hprojectionEq, hprojectionCard]
  exact hfiber

/-- Reverse triangle inequality in the form used by the dot separation. -/
private lemma wz1Lemma49_abs_rev_triangle
    (first second : ℝ) :
    |first + second| ≥ |first| - |second| := by
  have hrewrite :
      |first| = |(first + second) - second| := by
    congr 1
    ring
  rw [hrewrite]
  exact sub_le_iff_le_add.mpr (abs_sub _ _)

/-- Orthogonal-coordinate Pythagorean identity in `Point2`. -/
private lemma wz1Lemma49_norm_sq_orthogonal
    {direction : Point2} (hdirection : ‖direction‖ = 1)
    {vector : Point2} :
    ‖vector‖ ^ 2 =
      (inner ℝ vector direction) ^ 2 +
        (inner ℝ vector (wz1Perp2 direction)) ^ 2 := by
  have h := norm_cross_identity vector direction hdirection
  have hcross :
      cross2 vector direction =
        -inner ℝ vector (wz1Perp2 direction) := by
    simp [cross2, wz1Perp2, inner2_eq]
    ring
  rw [hcross] at h
  ring_nf at h ⊢
  exact h

/-- Expansion of a planar inner product in an orthonormal frame. -/
private lemma wz1Lemma49_inner_expansion
    {direction : Point2} (hdirection : ‖direction‖ = 1)
    {first vector : Point2} :
    inner ℝ first vector =
      inner ℝ first direction * inner ℝ vector direction +
        inner ℝ first (wz1Perp2 direction) *
          inner ℝ vector (wz1Perp2 direction) := by
  have hdirectionSq :
      direction 0 ^ 2 + direction 1 ^ 2 = 1 := by
    have hnorm :
        ‖direction‖ ^ 2 =
          direction 0 ^ 2 + direction 1 ^ 2 := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two,
        Real.sq_sqrt (by positivity :
          0 ≤ direction 0 ^ 2 + direction 1 ^ 2)]
    rw [hdirection] at hnorm
    norm_num at hnorm ⊢
    exact hnorm.symm
  have hleft :
      inner ℝ first vector =
        first 0 * vector 0 + first 1 * vector 1 := by
    exact inner2_eq first vector
  have hright :
      inner ℝ first direction * inner ℝ vector direction +
          inner ℝ first (wz1Perp2 direction) *
            inner ℝ vector (wz1Perp2 direction) =
        (first 0 * direction 0 + first 1 * direction 1) *
            (vector 0 * direction 0 + vector 1 * direction 1) +
          (first 0 * (-(direction 1)) +
              first 1 * direction 0) *
            (vector 0 * (-(direction 1)) +
              vector 1 * direction 0) := by
    simp [inner2_eq, wz1Perp2]
  rw [hleft, hright]
  calc
    first 0 * vector 0 + first 1 * vector 1 =
        (first 0 * vector 0 + first 1 * vector 1) *
          (direction 0 ^ 2 + direction 1 ^ 2) := by
      rw [hdirectionSq, mul_one]
    _ =
        (first 0 * direction 0 + first 1 * direction 1) *
            (vector 0 * direction 0 + vector 1 * direction 1) +
          (first 0 * (-(direction 1)) +
              first 1 * direction 0) *
            (vector 0 * (-(direction 1)) +
              vector 1 * direction 0) := by
      ring

/--
Points in one narrow active fiber become separated after applying the escaping
first-coordinate dot product.
-/
private lemma wz1Lemma49_dotdiff_separation
    {direction : Point2} (hdirection : ‖direction‖ = 1)
    {t R : ℝ} (ht : 0 < t) (hR : 0 < R) (hROne : R ≤ 1)
    {fiber : Finset Point2} {base : Point2}
    (hstrip :
      ∀ second ∈ fiber,
        |inner ℝ (second - base) (wz1Perp2 direction)| ≤ t)
    {first : Point2} (hfirstNorm : ‖first‖ ≤ 1)
    (hReq : R = |inner ℝ first direction|)
    {second other : Point2}
    (hsecond : second ∈ fiber) (hother : other ∈ fiber)
    (hne : second ≠ other)
    (hsep : 8 * t / R ≤ dist second other) :
    4 * Real.sqrt 3 * t - 2 * t ≤
      |inner ℝ first (second - other)| := by
  let perpendicular := wz1Perp2 direction
  let vector := second - other
  have hvectorNorm : 8 * t / R ≤ ‖vector‖ := by
    simpa [vector, dist_eq_norm] using hsep
  have hperpendicular :
      |inner ℝ vector perpendicular| ≤ 2 * t := by
    have hfirstStrip := hstrip second hsecond
    have hsecondStrip := hstrip other hother
    have heq :
        inner ℝ vector perpendicular =
          inner ℝ (second - base) perpendicular -
            inner ℝ (other - base) perpendicular := by
      simp [vector, inner_sub_left]
    rw [heq]
    exact (abs_sub _ _).trans (by linarith)
  have hnormSq :
      ‖vector‖ ^ 2 =
        (inner ℝ vector direction) ^ 2 +
          (inner ℝ vector perpendicular) ^ 2 :=
    wz1Lemma49_norm_sq_orthogonal hdirection
  have hperpendicularSq :
      (inner ℝ vector perpendicular) ^ 2 ≤ (2 * t) ^ 2 := by
    rw [show (inner ℝ vector perpendicular) ^ 2 =
      |inner ℝ vector perpendicular| ^ 2 by rw [sq_abs]]
    gcongr
  have hvectorFour : 4 * t ≤ ‖vector‖ := by
    have hscale : 8 * t ≤ 8 * t / R := by
      have hRinv : 1 ≤ 1 / R := by
        exact (le_div_iff₀ hR).mpr (by simpa using hROne)
      calc
        8 * t = 8 * t * 1 := by ring
        _ ≤ 8 * t * (1 / R) := by gcongr
        _ = 8 * t / R := by ring
    linarith
  have hdirectionLarge :
      (Real.sqrt 3 / 2) * ‖vector‖ ≤
        |inner ℝ vector direction| := by
    have hsquare :
        (3 / 4 : ℝ) * ‖vector‖ ^ 2 ≤
          (inner ℝ vector direction) ^ 2 := by
      have hsmall :
          (2 * t) ^ 2 ≤ (1 / 4 : ℝ) * ‖vector‖ ^ 2 := by
        nlinarith
      nlinarith
    have hsqrt : Real.sqrt 3 ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hleft :
        ((Real.sqrt 3 / 2) * ‖vector‖) ^ 2 =
          (3 / 4 : ℝ) * ‖vector‖ ^ 2 := by
      nlinarith
    rw [show (inner ℝ vector direction) ^ 2 =
      |inner ℝ vector direction| ^ 2 by rw [sq_abs]] at hsquare
    rw [← hleft] at hsquare
    nlinarith [Real.sqrt_nonneg 3, norm_nonneg vector,
      abs_nonneg (inner ℝ vector direction)]
  have hperpNorm : ‖perpendicular‖ = 1 := by
    have hsq :
        ‖perpendicular‖ ^ 2 = ‖direction‖ ^ 2 := by
      simp [perpendicular, wz1Perp2,
        EuclideanSpace.norm_eq, Fin.sum_univ_two]
      ring
    rw [hdirection] at hsq
    nlinarith [norm_nonneg perpendicular]
  have hfirstPerp :
      |inner ℝ first perpendicular| ≤ 1 := by
    calc
      |inner ℝ first perpendicular|
          ≤ ‖first‖ * ‖perpendicular‖ :=
        abs_real_inner_le_norm first perpendicular
      _ ≤ 1 * 1 := by
        rw [hperpNorm]
        gcongr
      _ = 1 := by ring
  have hexpansion :
      inner ℝ first vector =
        inner ℝ first direction * inner ℝ vector direction +
          inner ℝ first perpendicular *
            inner ℝ vector perpendicular :=
    wz1Lemma49_inner_expansion hdirection
  have hmain :
      R * |inner ℝ vector direction| -
          |inner ℝ first perpendicular| *
            |inner ℝ vector perpendicular| ≤
        |inner ℝ first vector| := by
    rw [hexpansion]
    have htriangle :=
      wz1Lemma49_abs_rev_triangle
        (inner ℝ first direction * inner ℝ vector direction)
        (inner ℝ first perpendicular *
          inner ℝ vector perpendicular)
    simpa [abs_mul, hReq] using htriangle
  have hdirectionTerm :
      4 * Real.sqrt 3 * t ≤
        R * |inner ℝ vector direction| := by
    calc
      4 * Real.sqrt 3 * t =
          R * ((Real.sqrt 3 / 2) * (8 * t / R)) := by
        field_simp [hR.ne']
        ring
      _ ≤ R * ((Real.sqrt 3 / 2) * ‖vector‖) := by
        gcongr
      _ ≤ R * |inner ℝ vector direction| := by
        gcongr
  have hperpTerm :
      |inner ℝ first perpendicular| *
          |inner ℝ vector perpendicular| ≤
        2 * t := by
    calc
      |inner ℝ first perpendicular| *
            |inner ℝ vector perpendicular|
          ≤ 1 * (2 * t) := by gcongr
      _ = 2 * t := by ring
  linarith

/--
Greedy selection of an `s`-separated subfamily with an explicit local
occupancy loss.
-/
private lemma wz1Lemma49_greedy_separated_subset
    {α : Type*} [MetricSpace α] [DecidableEq α]
    {source : Finset α} {s bound : ℝ}
    (hs : 0 < s) (hbound : 0 < bound)
    (hlocal :
      ∀ point : α,
        ((source.filter fun other =>
          dist point other ≤ s).card : ℝ) ≤ bound) :
    ∃ selected : Finset α,
      selected ⊆ source ∧
      (∀ first ∈ selected, ∀ second ∈ selected,
        first ≠ second → s < dist first second) ∧
      (source.card : ℝ) ≤ bound * (selected.card : ℝ) := by
  classical
  let separated (set : Finset α) : Prop :=
    ∀ first ∈ set, ∀ second ∈ set,
      first ≠ second → s < dist first second
  let candidates : Finset (Finset α) :=
    source.powerset.filter separated
  have hcandidates : candidates.Nonempty := by
    exact ⟨∅, by simp [candidates, separated]⟩
  rcases
      Finset.exists_max_image candidates
        (fun set : Finset α => set.card) hcandidates with
    ⟨selected, hselectedCandidate, hselectedMax⟩
  have hselected : selected ⊆ source :=
    Finset.mem_powerset.mp
      (Finset.mem_filter.mp hselectedCandidate).1
  have hseparated : separated selected :=
    (Finset.mem_filter.mp hselectedCandidate).2
  have hcover :
      ∀ point ∈ source,
        ∃ center ∈ selected, dist point center ≤ s := by
    intro point hpoint
    by_cases hpointSelected : point ∈ selected
    · exact ⟨point, hpointSelected, by
        simpa using hs.le⟩
    · by_contra hnone
      push Not at hnone
      let enlarged := insert point selected
      have henlargedSubset : enlarged ⊆ source := by
        intro current hcurrent
        rcases Finset.mem_insert.mp hcurrent with rfl | hcurrent
        · exact hpoint
        · exact hselected hcurrent
      have henlargedSeparated : separated enlarged := by
        intro first hfirst second hsecond hne
        rcases Finset.mem_insert.mp hfirst with hfirstEq | hfirstSelected
        · subst first
          rcases Finset.mem_insert.mp hsecond with hsecondEq | hsecondSelected
          · subst second
            exact False.elim (hne rfl)
          · exact hnone second hsecondSelected
        · rcases Finset.mem_insert.mp hsecond with hsecondEq | hsecondSelected
          · subst second
            rw [dist_comm]
            exact hnone first hfirstSelected
          · exact hseparated first hfirstSelected
              second hsecondSelected hne
      have henlargedCandidate : enlarged ∈ candidates := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr henlargedSubset,
            henlargedSeparated⟩
      have hcard := hselectedMax enlarged henlargedCandidate
      have henlargedCard :
          enlarged.card = selected.card + 1 := by
        exact Finset.card_insert_of_notMem hpointSelected
      omega
  let neighborhood (center : α) : Finset α :=
    source.filter fun point => dist point center ≤ s
  have hsourceSubset :
      source ⊆ selected.biUnion neighborhood := by
    intro point hpoint
    rcases hcover point hpoint with
      ⟨center, hcenter, hdist⟩
    exact Finset.mem_biUnion.mpr
      ⟨center, hcenter,
        Finset.mem_filter.mpr ⟨hpoint, hdist⟩⟩
  have hcardNat :
      source.card ≤
        ∑ center ∈ selected, (neighborhood center).card := by
    exact
      (Finset.card_le_card hsourceSubset).trans
        Finset.card_biUnion_le
  have hcardReal :
      (source.card : ℝ) ≤
        ∑ center ∈ selected,
          ((neighborhood center).card : ℝ) := by
    exact_mod_cast hcardNat
  have hneighborhood :
      ∀ center ∈ selected,
        ((neighborhood center).card : ℝ) ≤ bound := by
    intro center _
    have h := hlocal center
    have heq :
        neighborhood center =
          source.filter fun point => dist center point ≤ s := by
      ext point
      simp [neighborhood, dist_comm]
    rw [← heq] at h
    exact h
  refine ⟨selected, hselected, hseparated, ?_⟩
  calc
    (source.card : ℝ)
        ≤ ∑ center ∈ selected,
            ((neighborhood center).card : ℝ) :=
      hcardReal
    _ ≤ ∑ _center ∈ selected, bound := by
      exact Finset.sum_le_sum hneighborhood
    _ = bound * (selected.card : ℝ) := by
      simp [Finset.sum_const]
      ring

/--
The dot images of a sufficiently separated active fiber lie in one short
interval and retain their full cardinality in the dot-difference set.
-/
private theorem wz1Lemma49_active_fiber_dot_covering
    {t R : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    {direction base first third : Point2}
    {fiber selected : Finset Point2}
    (ht : 0 < t) (hR : 0 < R) (hRTwenty : 20 * t ≤ R)
    (hdirection : ‖direction‖ = 1)
    (hfiberStrip :
      ∀ second ∈ fiber,
        |inner ℝ (second - base) (wz1Perp2 direction)| ≤ t)
    (hfiberDiameter :
      ∀ second ∈ fiber, ∀ other ∈ fiber,
        dist second other ≤ 1 / 10)
    (hfirstNorm : ‖first‖ ≤ 1)
    (hReq : R = |inner ℝ first direction|)
    (hselectedSubset : selected ⊆ fiber)
    (hselectedSeparated :
      ∀ second ∈ selected, ∀ other ∈ selected,
        second ≠ other → 8 * t / R < dist second other)
    (hfiberEdges :
      ∀ second ∈ fiber, (first, second, third) ∈ H)
    (hselectedNonempty : selected.Nonempty) :
    ∃ center : ℝ,
      (selected.card : ENNReal) ≤
        Metric.externalCoveringNumber
          (Real.toNNReal t)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall center (R / 5)) := by
  let dotValue : Point2 → ℝ :=
    fun second => inner ℝ first (second - third)
  have hdotSub :
      ∀ second other : Point2,
        dotValue second - dotValue other =
          inner ℝ first (second - other) := by
    intro second other
    simp [dotValue, inner_sub_right]
  let values : Finset ℝ := selected.image dotValue
  have hdotInjective :
      Set.InjOn dotValue (selected : Set Point2) := by
    intro second hsecond other hother heq
    by_contra hne
    have hsep :=
      hselectedSeparated second hsecond other hother hne
    have hdotLarge :
        4 * Real.sqrt 3 * t - 2 * t ≤
          |inner ℝ first (second - other)| :=
      wz1Lemma49_dotdiff_separation
        hdirection ht hR
        (by
          have hfirstFiber := hselectedSubset hsecond
          have hotherFiber := hselectedSubset hother
          have hdiameter :=
            hfiberDiameter second hfirstFiber other hotherFiber
          have hnorm :
              |inner ℝ first direction| ≤
                ‖first‖ * ‖direction‖ :=
            abs_real_inner_le_norm first direction
          rw [hdirection, mul_one, ← hReq] at hnorm
          linarith)
        hfiberStrip hfirstNorm hReq
        (hselectedSubset hsecond)
        (hselectedSubset hother) hne hsep.le
    have hzero :
        inner ℝ first (second - other) = 0 := by
      have h := congrArg
        (fun value => value - dotValue other) heq
      simpa [hdotSub second other] using h
    rw [hzero, abs_zero] at hdotLarge
    have hsqrt : 3 / 2 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    nlinarith
  have hvaluesCard : values.card = selected.card :=
    Finset.card_image_of_injOn hdotInjective
  have hvaluesSeparated :
      ∀ firstValue ∈ values, ∀ secondValue ∈ values,
        firstValue ≠ secondValue →
          2 * t < |firstValue - secondValue| := by
    intro firstValue hfirstValue secondValue hsecondValue hne
    rcases Finset.mem_image.mp hfirstValue with
      ⟨second, hsecond, rfl⟩
    rcases Finset.mem_image.mp hsecondValue with
      ⟨other, hother, rfl⟩
    have hnePoints : second ≠ other := by
      intro heq
      subst other
      exact hne rfl
    have hsep :=
      hselectedSeparated second hsecond other hother hnePoints
    have hROne : R ≤ 1 := by
      have hnorm :
          |inner ℝ first direction| ≤
            ‖first‖ * ‖direction‖ :=
        abs_real_inner_le_norm first direction
      rw [hdirection, mul_one, ← hReq] at hnorm
      exact hnorm.trans hfirstNorm
    have hdotLarge :=
      wz1Lemma49_dotdiff_separation
        hdirection ht hR hROne hfiberStrip
        hfirstNorm hReq
        (hselectedSubset hsecond)
        (hselectedSubset hother) hnePoints hsep.le
    rw [hdotSub]
    have hsqrt : 3 / 2 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    nlinarith
  have hcoverValues :=
    wz1Lemma49_separated_real_covering_lower_bound
      ht hvaluesSeparated
  have hvaluesDot :
      (values : Set ℝ) ⊆ wz1DotDifferenceSet H := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨second, hsecond, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(first, second, third),
        hfiberEdges second (hselectedSubset hsecond),
        rfl⟩
  let reference := Classical.choose hselectedNonempty
  let center := dotValue reference
  have hreference : reference ∈ selected :=
    Classical.choose_spec hselectedNonempty
  have hperpNorm : ‖wz1Perp2 direction‖ = 1 := by
    have hsq :
        ‖wz1Perp2 direction‖ ^ 2 = ‖direction‖ ^ 2 := by
      rw [norm2_sq, norm2_sq]
      simp [wz1Perp2]
      ring
    rw [hdirection] at hsq
    nlinarith [norm_nonneg (wz1Perp2 direction)]
  have hfirstPerp :
      |inner ℝ first (wz1Perp2 direction)| ≤ 1 := by
    calc
      |inner ℝ first (wz1Perp2 direction)|
          ≤ ‖first‖ * ‖wz1Perp2 direction‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 := by
        rw [hperpNorm, mul_one]
        exact hfirstNorm
  have hvaluesBall :
      (values : Set ℝ) ⊆
        Metric.closedBall center (R / 5) := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨second, hsecond, rfl⟩
    have hsecondFiber := hselectedSubset hsecond
    have hreferenceFiber := hselectedSubset hreference
    have hdiameter :=
      hfiberDiameter second hsecondFiber
        reference hreferenceFiber
    have hparallel :
        |inner ℝ (second - reference) direction| ≤
          1 / 10 := by
      calc
        |inner ℝ (second - reference) direction|
            ≤ ‖second - reference‖ * ‖direction‖ :=
          abs_real_inner_le_norm _ _
        _ = dist second reference := by
          rw [hdirection, mul_one]
          simp [dist_eq_norm]
        _ ≤ 1 / 10 := hdiameter
    have hperpendicular :
        |inner ℝ (second - reference)
            (wz1Perp2 direction)| ≤ 2 * t := by
      have hsecondStrip := hfiberStrip second hsecondFiber
      have hrefStrip := hfiberStrip reference hreferenceFiber
      have heq :
          inner ℝ (second - reference)
              (wz1Perp2 direction) =
            inner ℝ (second - base)
                (wz1Perp2 direction) -
              inner ℝ (reference - base)
                (wz1Perp2 direction) := by
        simp [inner_sub_left]
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
    have hparallelTerm :
        R * |inner ℝ (second - reference) direction| ≤
          R * (1 / 10) :=
      mul_le_mul_of_nonneg_left hparallel hR.le
    have hperpTerm :
        |inner ℝ first (wz1Perp2 direction)| *
            |inner ℝ (second - reference)
              (wz1Perp2 direction)| ≤
          2 * t := by
      calc
        |inner ℝ first (wz1Perp2 direction)| *
              |inner ℝ (second - reference)
                (wz1Perp2 direction)|
            ≤ 1 * |inner ℝ (second - reference)
                (wz1Perp2 direction)| := by
          gcongr
        _ ≤ 1 * (2 * t) := by gcongr
        _ = 2 * t := by ring
    have hdotBound :
        |inner ℝ first (second - reference)| ≤
          R * (1 / 10) + 2 * t := by
      rw [wz1Lemma49_inner_expansion hdirection]
      calc
        |inner ℝ first direction *
              inner ℝ (second - reference) direction +
            inner ℝ first (wz1Perp2 direction) *
              inner ℝ (second - reference)
                (wz1Perp2 direction)|
            ≤
          |inner ℝ first direction *
              inner ℝ (second - reference) direction| +
            |inner ℝ first (wz1Perp2 direction) *
              inner ℝ (second - reference)
                (wz1Perp2 direction)| := abs_add_le _ _
        _ =
          R * |inner ℝ (second - reference) direction| +
            |inner ℝ first (wz1Perp2 direction)| *
              |inner ℝ (second - reference)
                (wz1Perp2 direction)| := by
          rw [abs_mul, abs_mul, ← hReq]
        _ ≤ R * (1 / 10) + 2 * t :=
          add_le_add hparallelTerm hperpTerm
    have htwoT : 2 * t ≤ R / 10 := by
      linarith
    have hdistance :
        |dotValue second - center| ≤ R / 5 := by
      change
        |dotValue second - dotValue reference| ≤ R / 5
      rw [hdotSub]
      calc
        |inner ℝ first (second - reference)|
            ≤ R * (1 / 10) + 2 * t := hdotBound
        _ ≤ R * (1 / 10) + R / 10 := by gcongr
        _ = R / 5 := by ring
    simpa [Metric.mem_closedBall, Real.dist_eq] using hdistance
  have hvaluesIntersection :
      (values : Set ℝ) ⊆
        wz1DotDifferenceSet H ∩
          Metric.closedBall center (R / 5) :=
    fun value hvalue =>
      ⟨hvaluesDot hvalue, hvaluesBall hvalue⟩
  have hcoverMono :
      Metric.externalCoveringNumber
          (Real.toNNReal t) (values : Set ℝ) ≤
        Metric.externalCoveringNumber
          (Real.toNNReal t)
          (wz1DotDifferenceSet H ∩
            Metric.closedBall center (R / 5)) :=
    Metric.externalCoveringNumber_mono_set hvaluesIntersection
  refine ⟨center, ?_⟩
  rw [← hvaluesCard]
  exact hcoverValues.trans (by exact_mod_cast hcoverMono)

/-- Pure exponent bookkeeping for the direct outside-strip branch. -/
private theorem wz1Lemma49_outside_active_strip_exponent
    {delta epsilon eta epsilonHalf t R : ℝ}
    {selected : Finset Point2}
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (ht : 0 < t) (hR : 0 < R)
    (hRLower :
      (1 / 4 : ℝ) * Real.rpow delta (-epsilonHalf) * t ≤ R)
    (hconstant :
      (16 / 5 : ℝ) ^ (1 - epsilon) * 32 ^ epsilon ≤
        Real.rpow delta (2 * eta - epsilonHalf * epsilon))
    (hselectedSize :
      Real.rpow delta (2 * eta) / (8 * t / R) ≤
        (selected.card : ℝ)) :
    Kakeya.realRpowENN
        (2 * (R / 5) / t) (1 - epsilon) ≤
      (selected.card : ENNReal) := by
  let separation := 8 * t / R
  have hseparation : 0 < separation := by
    dsimp only [separation]
    positivity
  have hseparationUpper :
      separation ≤ 32 * Real.rpow delta epsilonHalf := by
    have hinverse :
        Real.rpow delta (-epsilonHalf) =
          (Real.rpow delta epsilonHalf)⁻¹ :=
      Real.rpow_neg hdelta.le epsilonHalf
    have hpowPos :
        0 < Real.rpow delta epsilonHalf :=
      Real.rpow_pos_of_pos hdelta _
    dsimp only [separation]
    calc
      8 * t / R
          ≤
        8 * t /
          ((1 / 4 : ℝ) *
            Real.rpow delta (-epsilonHalf) * t) := by
        apply div_le_div_of_nonneg_left
          (by positivity)
          (mul_pos
            (mul_pos (by norm_num)
              (Real.rpow_pos_of_pos hdelta _)) ht)
          hRLower
      _ = 32 * Real.rpow delta epsilonHalf := by
        rw [hinverse]
        field_simp [hpowPos.ne', ht.ne']
        ring
  have hsepPower :
      separation ^ epsilon ≤
        32 ^ epsilon *
          Real.rpow delta (epsilonHalf * epsilon) := by
    calc
      separation ^ epsilon
          ≤ (32 * Real.rpow delta epsilonHalf) ^ epsilon :=
        Real.rpow_le_rpow hseparation.le
          hseparationUpper hepsilon.le
      _ =
          32 ^ epsilon *
            (Real.rpow delta epsilonHalf) ^ epsilon := by
        exact Real.mul_rpow (by norm_num)
          (Real.rpow_nonneg hdelta.le _)
      _ =
          32 ^ epsilon *
            Real.rpow delta (epsilonHalf * epsilon) := by
        congr 1
        exact
          (Real.rpow_mul hdelta.le
            epsilonHalf epsilon).symm
  have hpowerBudget :
      (16 / 5 : ℝ) ^ (1 - epsilon) *
          separation ^ epsilon ≤
        Real.rpow delta (2 * eta) := by
    calc
      (16 / 5 : ℝ) ^ (1 - epsilon) *
            separation ^ epsilon
          ≤
        ((16 / 5 : ℝ) ^ (1 - epsilon) *
            32 ^ epsilon) *
          Real.rpow delta
            (epsilonHalf * epsilon) := by
        calc
          (16 / 5 : ℝ) ^ (1 - epsilon) *
                separation ^ epsilon
              ≤
            (16 / 5 : ℝ) ^ (1 - epsilon) *
              (32 ^ epsilon *
                Real.rpow delta
                  (epsilonHalf * epsilon)) := by
            gcongr
          _ = _ := by ring
      _ ≤
        Real.rpow delta
            (2 * eta - epsilonHalf * epsilon) *
          Real.rpow delta
            (epsilonHalf * epsilon) := by
        exact mul_le_mul_of_nonneg_right hconstant
          (Real.rpow_nonneg hdelta.le _)
      _ =
        Real.rpow delta
          ((2 * eta - epsilonHalf * epsilon) +
            epsilonHalf * epsilon) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (2 * eta) := by
        congr 1
        ring
  have hratio :
      2 * (R / 5) / t = 16 / (5 * separation) := by
    dsimp only [separation]
    field_simp [hR.ne', ht.ne']
    ring
  have hbaseRewrite :
      Real.rpow (16 / (5 * separation))
          (1 - epsilon) =
        (16 / 5 : ℝ) ^ (1 - epsilon) *
          separation ^ (epsilon - 1) := by
    have hfactor :
        16 / (5 * separation) =
          (16 / 5 : ℝ) * separation⁻¹ := by
      field_simp [hseparation.ne']
    rw [hfactor]
    calc
      Real.rpow ((16 / 5 : ℝ) * separation⁻¹)
            (1 - epsilon)
          =
        (16 / 5 : ℝ) ^ (1 - epsilon) *
          Real.rpow separation⁻¹ (1 - epsilon) :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ =
        (16 / 5 : ℝ) ^ (1 - epsilon) *
          Real.rpow (Real.rpow separation (-1 : ℝ))
            (1 - epsilon) := by
        rw [show separation⁻¹ =
          Real.rpow separation (-1 : ℝ) by
            exact (Real.rpow_neg_one separation).symm]
      _ =
        (16 / 5 : ℝ) ^ (1 - epsilon) *
          Real.rpow separation
            ((-1 : ℝ) * (1 - epsilon)) := by
        congr 1
        exact
          (Real.rpow_mul hseparation.le
            (-1 : ℝ) (1 - epsilon)).symm
      _ =
        (16 / 5 : ℝ) ^ (1 - epsilon) *
          separation ^ (epsilon - 1) := by
        congr 2
        ring
  have hsepDiv :
      separation ^ epsilon / separation =
        separation ^ (epsilon - 1) := by
    calc
      separation ^ epsilon / separation =
          separation ^ epsilon /
            separation ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = separation ^ (epsilon - 1) :=
        (Real.rpow_sub hseparation epsilon 1).symm
  have hexponentBudget :
      Real.rpow (2 * (R / 5) / t) (1 - epsilon) ≤
        Real.rpow delta (2 * eta) / separation := by
    rw [hratio, hbaseRewrite]
    calc
      (16 / 5 : ℝ) ^ (1 - epsilon) *
            separation ^ (epsilon - 1)
          =
        ((16 / 5 : ℝ) ^ (1 - epsilon) *
            separation ^ epsilon) / separation := by
        rw [mul_div_assoc, hsepDiv]
      _ ≤ Real.rpow delta (2 * eta) / separation := by
        gcongr
  rw [Kakeya.realRpowENN]
  apply (ENNReal.ofReal_le_natCast).2
  exact hexponentBudget.trans
    (by simpa [separation] using hselectedSize)

/--
Quantitative direct branch: a dense active fiber in a strip, tested against
an escaping first-coordinate vertex, gives the required long dot projection.
-/
theorem wz1_lemma49_outside_active_strip_core
    {delta epsilon eta epsilonHalf t R : ℝ}
    {G₁ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {direction base first third : Point2}
    {fiber : Finset Point2}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hepsilonHalf : 0 < epsilonHalf)
    (hexponent : 2 * eta < epsilonHalf * epsilon)
    (ht : 0 < t) (hdeltaT : delta ≤ t) (htOne : t ≤ 1)
    (hR : 0 < R) (hROne : R ≤ 1)
    (hRLower :
      (1 / 4 : ℝ) * Real.rpow delta (-epsilonHalf) * t ≤ R)
    (hRTwenty : 20 * t ≤ R)
    (hseparationScale : 8 * t / R ≤ 1)
    (hconstant :
      (16 / 5 : ℝ) ^ (1 - epsilon) * 32 ^ epsilon ≤
        Real.rpow delta (2 * eta - epsilonHalf * epsilon))
    (hradius :
      Real.rpow delta (-eta) * t ≤ 2 * (R / 5))
    (hdirection : ‖direction‖ = 1)
    (hfiberStrip :
      ∀ second ∈ fiber,
        |inner ℝ (second - base) (wz1Perp2 direction)| ≤ t)
    (hG₁Frostman :
      G₁.IsFrostman delta 1
        (Kakeya.realRpowENN delta (-eta)))
    (hG₁Nonempty : G₁.Nonempty)
    (hG₁Diameter :
      ∀ second ∈ G₁, ∀ other ∈ G₁,
        dist second other ≤ 1 / 10)
    (hfirstNorm : ‖first‖ ≤ 1)
    (hReq : R = |inner ℝ first direction|)
    (hfiberSubset : fiber ⊆ G₁)
    (hfiberSize :
      Real.rpow delta eta * (G₁.card : ℝ) ≤
        (fiber.card : ℝ))
    (hfiberEdges :
      ∀ second ∈ fiber, (first, second, third) ∈ H) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H := by
  let separation := 8 * t / R
  have hseparation : 0 < separation := by
    dsimp only [separation]
    positivity
  have hseparationDelta : delta ≤ separation := by
    have htEight : t ≤ 8 * t := by linarith
    have hratio : 8 * t ≤ 8 * t / R := by
      exact (le_div_iff₀ hR).mpr
        (by nlinarith [hROne, ht])
    exact hdeltaT.trans (htEight.trans hratio)
  let localBound :=
    Real.rpow delta (-eta) * separation * (G₁.card : ℝ)
  have hG₁Card : 0 < (G₁.card : ℝ) := by
    exact_mod_cast hG₁Nonempty.card_pos
  have hlocalBound : 0 < localBound := by
    dsimp only [localBound]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hdelta _) hseparation)
      hG₁Card
  have hambientLocal :
      ∀ point : Point2,
        ((G₁.filter fun other =>
          dist point other ≤ separation).card : ℝ) ≤
          localBound := by
    intro point
    have h :=
      frostman_real_bound
        (x := point) hdelta
        (Real.rpow_nonneg hdelta.le (-eta))
        (by simpa [Kakeya.realRpowENN] using hG₁Frostman)
        hseparationDelta hseparationScale
    have heq :
        G₁.filter (fun other => dist other point ≤ separation) =
          G₁.filter (fun other => dist point other ≤ separation) := by
      ext other
      simp [dist_comm]
    rw [heq] at h
    simpa [localBound, Real.rpow_one] using h
  have hfiberLocal :
      ∀ point : Point2,
        ((fiber.filter fun other =>
          dist point other ≤ separation).card : ℝ) ≤
          localBound := by
    intro point
    have hsubset :
        fiber.filter (fun other =>
            dist point other ≤ separation) ⊆
          G₁.filter (fun other =>
            dist point other ≤ separation) := by
      intro other hother
      exact Finset.mem_filter.mpr
        ⟨hfiberSubset (Finset.mem_filter.mp hother).1,
          (Finset.mem_filter.mp hother).2⟩
    have hcard :
        ((fiber.filter fun other =>
          dist point other ≤ separation).card : ℝ) ≤
          ((G₁.filter fun other =>
            dist point other ≤ separation).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcard.trans (hambientLocal point)
  rcases
      wz1Lemma49_greedy_separated_subset
        hseparation hlocalBound hfiberLocal with
    ⟨selected, hselectedSubset, hselectedSeparated,
      hfiberSelected⟩
  have hselectedG₁ : selected ⊆ G₁ :=
    hselectedSubset.trans hfiberSubset
  have hselectedSize :
      Real.rpow delta (2 * eta) / separation ≤
        (selected.card : ℝ) := by
    have hrpowCancel :
        Real.rpow delta (-eta) *
            Real.rpow delta eta = 1 := by
      have h := (Real.rpow_add hdelta (-eta) eta).symm
      simpa using h
    have hmain :
        Real.rpow delta eta * (G₁.card : ℝ) ≤
          (Real.rpow delta (-eta) * separation *
              (G₁.card : ℝ)) *
            (selected.card : ℝ) :=
      hfiberSize.trans hfiberSelected
    have hcancel :
        Real.rpow delta eta ≤
          Real.rpow delta (-eta) * separation *
            (selected.card : ℝ) := by
      calc
        Real.rpow delta eta =
            (Real.rpow delta eta * (G₁.card : ℝ)) /
              (G₁.card : ℝ) := by
          field_simp [hG₁Card.ne']
        _ ≤
            ((Real.rpow delta (-eta) * separation *
                (G₁.card : ℝ)) *
              (selected.card : ℝ)) /
                (G₁.card : ℝ) := by
          gcongr
        _ =
            Real.rpow delta (-eta) * separation *
              (selected.card : ℝ) := by
          field_simp [hG₁Card.ne']
    have hsquare :
        Real.rpow delta (2 * eta) ≤
          (selected.card : ℝ) * separation := by
      have hpow :
          Real.rpow delta (2 * eta) =
            Real.rpow delta eta *
              Real.rpow delta eta := by
        simpa [two_mul] using
          Real.rpow_add hdelta eta eta
      rw [hpow]
      calc
        Real.rpow delta eta * Real.rpow delta eta
            ≤
          (Real.rpow delta (-eta) * separation *
              (selected.card : ℝ)) *
            Real.rpow delta eta := by
          exact mul_le_mul_of_nonneg_right hcancel
            (Real.rpow_nonneg hdelta.le eta)
        _ = (selected.card : ℝ) * separation := by
          rw [show
            Real.rpow delta (-eta) * separation *
                  (selected.card : ℝ) *
                Real.rpow delta eta =
              (selected.card : ℝ) *
                (Real.rpow delta (-eta) *
                  Real.rpow delta eta) * separation by ring,
            hrpowCancel]
          ring
    exact (div_le_iff₀ hseparation).2
      (by simpa [mul_comm] using hsquare)
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ := by
      simpa using hempty
    have hpositive :
        0 < Real.rpow delta (2 * eta) / separation := by
      exact div_pos
        (Real.rpow_pos_of_pos hdelta _) hseparation
    rw [hselectedEmpty] at hselectedSize
    norm_num at hselectedSize
    exact (not_lt_of_ge hselectedSize) hpositive
  have hfiberDiameter :
      ∀ second ∈ fiber, ∀ other ∈ fiber,
        dist second other ≤ 1 / 10 := by
    intro second hsecond other hother
    exact
      hG₁Diameter second (hfiberSubset hsecond)
        other (hfiberSubset hother)
  rcases
      wz1Lemma49_active_fiber_dot_covering
        ht hR hRTwenty hdirection
        hfiberStrip hfiberDiameter hfirstNorm hReq
        hselectedSubset
        (by
          intro second hsecond other hother hne
          simpa [separation] using
            hselectedSeparated second hsecond other hother hne)
        hfiberEdges hselectedNonempty with
    ⟨center, hcover⟩
  have hcard :
      Kakeya.realRpowENN
          (2 * (R / 5) / t) (1 - epsilon) ≤
        (selected.card : ENNReal) :=
    wz1Lemma49_outside_active_strip_exponent
      hdelta hepsilon ht hR hRLower hconstant
      (by simpa [separation] using hselectedSize)
  exact
    ⟨t, center, R / 5, hdeltaT, htOne,
      by positivity, hradius, hcard.trans hcover⟩

end

end Kakeya.Assouad
