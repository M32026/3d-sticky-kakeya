import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointLocalization
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23Theorem22ReadyGraph

/-!
# Bad-edge counting for the common-endpoint projection graph

The final Theorem-22 reduction removes edges with `a` close to the origin
or `b₁` close to `b₂`.  Because both endpoint coordinates live in one
ambient Katz--Tao set, both losses are controlled by the same absolute
one-dimensional non-concentration estimate.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- A Katz--Tao set contained in the unit ball has the expected absolute
cardinality upper bound. -/
lemma katzTao_unit_ball_card
    {A : DiscreteSet 2} {delta : ℝ} {C : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hA : A.IsInUnitBall)
    (hKT : A.IsKatzTao delta 1 C) :
    A.enncard ≤ C * Kakeya.realRpowENN (1 / delta) 1 := by
  have hfilter : A.filter (fun point => dist point 0 ≤ 1) = A := by
    ext point
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hpoint
      exact ⟨hpoint, hA point hpoint⟩
  have hball : A.ballCount 0 1 = A.enncard := by
    change ((A.filter fun point => dist point 0 ≤ 1).card : ENNReal) =
      (A.card : ENNReal)
    rw [hfilter]
  rw [← hball]
  exact hKT 0 1 hdeltaOne (le_rfl)

/-- Absolute Katz--Tao control of a ball inside the ambient endpoint set. -/
lemma katzTao_ball_card
    {A : DiscreteSet 2} {delta radius : ℝ} {C : ENNReal}
    (hKT : A.IsKatzTao delta 1 C)
    (hdeltaRadius : delta ≤ radius) (hradiusOne : radius ≤ 1)
    (center : Point2) :
    ((A.filter fun point => dist point center ≤ radius).card : ENNReal) ≤
      C * Kakeya.realRpowENN (radius / delta) 1 := by
  simpa [DiscreteSet.ballCount] using
    hKT center radius hdeltaRadius hradiusOne

/-- Supported edges whose first coordinate belongs to `badF` are bounded by
the full product of `badF` with the two ambient endpoint classes. -/
lemma supported_first_bad_card
    {F G badF : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G ∧ edge.2.2 ∈ G)
    (hbad : badF ⊆ F) :
    (H.filter fun edge => edge.1 ∈ badF).card ≤
      badF.card * G.card * G.card := by
  let target : Finset (Point2 × Point2 × Point2) :=
    badF.product (G.product G)
  have hsub : (H.filter fun edge => edge.1 ∈ badF) ⊆ target := by
    intro edge hedge
    have hedgeH := (Finset.mem_filter.mp hedge).1
    have hedgeBad := (Finset.mem_filter.mp hedge).2
    have hs := hsupport edge hedgeH
    exact Finset.mem_product.mpr
      ⟨hedgeBad, Finset.mem_product.mpr ⟨hs.2.1, hs.2.2⟩⟩
  calc
    (H.filter fun edge => edge.1 ∈ badF).card
        ≤ target.card := Finset.card_le_card hsub
    _ = badF.card * G.card * G.card := by
      simp [target, Finset.card_product, Nat.mul_assoc]

/-- Supported edges with a close endpoint pair are bounded by the number of
close ordered endpoint pairs times the size of the first ambient class. -/
lemma supported_close_endpoints_card
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G ∧ edge.2.2 ∈ G)
    (threshold : ℝ) :
    (H.filter fun edge => dist edge.2.1 edge.2.2 < threshold).card ≤
      F.card *
        ((G.product G).filter fun pair =>
          dist pair.1 pair.2 < threshold).card := by
  let closePairs :=
    (G.product G).filter fun pair => dist pair.1 pair.2 < threshold
  let target : Finset (Point2 × Point2 × Point2) :=
    F.product closePairs
  have hsub :
      (H.filter fun edge => dist edge.2.1 edge.2.2 < threshold) ⊆
        target := by
    intro edge hedge
    have hedgeH := (Finset.mem_filter.mp hedge).1
    have hedgeClose := (Finset.mem_filter.mp hedge).2
    have hs := hsupport edge hedgeH
    exact Finset.mem_product.mpr
      ⟨hs.1, Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs.2.1, hs.2.2⟩, hedgeClose⟩⟩
  calc
    (H.filter fun edge => dist edge.2.1 edge.2.2 < threshold).card
        ≤ target.card := Finset.card_le_card hsub
    _ = F.card * closePairs.card := Finset.card_product F closePairs
    _ = F.card *
          ((G.product G).filter fun pair =>
            dist pair.1 pair.2 < threshold).card := rfl

/-- Count close ordered endpoint pairs by summing one Katz--Tao ball over
the first endpoint.  The strict predicate is weakened to the closed ball
predicate required by `ballCount`. -/
lemma close_endpoint_pairs_card
    {G : DiscreteSet 2} {delta threshold : ℝ} {C : ENNReal}
    (hKT : G.IsKatzTao delta 1 C)
    (hdeltaThreshold : delta ≤ threshold)
    (hthresholdOne : threshold ≤ 1) :
    (((G.product G).filter fun pair =>
      dist pair.1 pair.2 < threshold).card : ENNReal) ≤
      G.enncard *
        (C * Kakeya.realRpowENN (threshold / delta) 1) := by
  let closeStrict :=
    (G.product G).filter fun pair => dist pair.1 pair.2 < threshold
  let closeClosed :=
    (G.product G).filter fun pair => dist pair.1 pair.2 ≤ threshold
  have hsub : closeStrict ⊆ closeClosed := by
    intro pair hpair
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hpair).1,
        (Finset.mem_filter.mp hpair).2.le⟩
  have hclosed :
      closeClosed.card =
        ∑ first ∈ G,
          (G.filter fun second => dist first second ≤ threshold).card := by
    let fiber : Point2 → Finset (Point2 × Point2) := fun first =>
      (G.filter fun second => dist first second ≤ threshold).image
        (fun second => (first, second))
    have hdisjoint :
        ∀ first ∈ G, ∀ other ∈ G, first ≠ other →
          Disjoint (fiber first) (fiber other) := by
      intro first _ other _ hne
      rw [Finset.disjoint_left]
      intro pair hfirst hother
      rcases Finset.mem_image.mp hfirst with ⟨second, _, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨third, _, heq⟩
      exact hne (congr_arg Prod.fst heq).symm
    have hunion : closeClosed = G.biUnion fiber := by
      apply Finset.ext
      rintro ⟨first, second⟩
      constructor
      · intro hpair
        have hpair' := Finset.mem_filter.mp hpair
        have hmem := Finset.mem_product.mp hpair'.1
        apply Finset.mem_biUnion.mpr
        refine ⟨first, hmem.1, ?_⟩
        apply Finset.mem_image.mpr
        exact ⟨second, Finset.mem_filter.mpr ⟨hmem.2, hpair'.2⟩, rfl⟩
      · intro hpair
        rcases Finset.mem_biUnion.mp hpair with ⟨other, hother, himage⟩
        rcases Finset.mem_image.mp himage with ⟨endpoint, hendpoint, heq⟩
        have hfirst : other = first := congr_arg Prod.fst heq
        have hsecond : endpoint = second := congr_arg Prod.snd heq
        subst other
        subst endpoint
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨hother, (Finset.mem_filter.mp hendpoint).1⟩,
           (Finset.mem_filter.mp hendpoint).2⟩
    rw [hunion, Finset.card_biUnion hdisjoint]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.card_image_of_injective]
    intro second third heq
    exact congr_arg Prod.snd heq
  have hfiber :
      ∀ first ∈ G,
        ((G.filter fun second =>
          dist first second ≤ threshold).card : ENNReal) ≤
          C * Kakeya.realRpowENN (threshold / delta) 1 := by
    intro first _
    have h := katzTao_ball_card hKT hdeltaThreshold hthresholdOne first
    simpa [dist_comm] using h
  calc
    (closeStrict.card : ENNReal)
        ≤ (closeClosed.card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hsub
    _ = ∑ first ∈ G,
          ((G.filter fun second =>
            dist first second ≤ threshold).card : ENNReal) := by
          exact_mod_cast hclosed
    _ ≤ ∑ _first ∈ G,
          (C * Kakeya.realRpowENN (threshold / delta) 1) := by
          exact Finset.sum_le_sum hfiber
    _ = G.enncard *
          (C * Kakeya.realRpowENN (threshold / delta) 1) := by
          simp [DiscreteSet.enncard, Finset.sum_const]
    _ = G.enncard *
          (C * Kakeya.realRpowENN (threshold / delta) 1) := rfl

/-- The original graph is covered by its good part and the two literal bad
parts.  This is kept as a cardinality inequality because the two bad parts
may overlap. -/
lemma common_endpoint_good_bad_cover_card
    {threshold : ℝ}
    {H : Finset (Point2 × Point2 × Point2)} :
    (H.card : ENNReal) ≤
      (wz1CommonEndpointGoodEdges threshold H).card +
        (H.filter fun edge => dist edge.1 0 < threshold).card +
        (H.filter fun edge =>
          dist edge.2.1 edge.2.2 < threshold).card := by
  let good := wz1CommonEndpointGoodEdges threshold H
  let badFirst := H.filter fun edge => dist edge.1 0 < threshold
  let badEndpoints :=
    H.filter fun edge => dist edge.2.1 edge.2.2 < threshold
  have hcover : H ⊆ (good ∪ badFirst) ∪ badEndpoints := by
    intro edge hedge
    by_cases hfirst : threshold ≤ dist edge.1 0
    · by_cases hendpoints : threshold ≤ dist edge.2.1 edge.2.2
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hedge, hfirst, hendpoints⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hedge, lt_of_not_ge hendpoints⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hedge, lt_of_not_ge hfirst⟩))
  have hnat :
      H.card ≤ good.card + badFirst.card + badEndpoints.card := by
    calc
      H.card ≤ ((good ∪ badFirst) ∪ badEndpoints).card :=
        Finset.card_le_card hcover
      _ ≤ (good ∪ badFirst).card + badEndpoints.card :=
        Finset.card_union_le _ _
      _ ≤ (good.card + badFirst.card) + badEndpoints.card := by
        gcongr
        exact Finset.card_union_le _ _
  exact_mod_cast hnat

/-- Quantitative common-endpoint bad-edge bound. -/
lemma common_endpoint_good_edge_lower_bound
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {delta threshold : ℝ} {C : ENNReal}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G ∧ edge.2.2 ∈ G)
    (hFball : F.IsInUnitBall) (hGball : G.IsInUnitBall)
    (hFkt : F.IsKatzTao delta 1 C)
    (hGkt : G.IsKatzTao delta 1 C)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ threshold)
    (hthresholdOne : threshold ≤ 1) :
    (H.card : ENNReal) ≤
      (wz1CommonEndpointGoodEdges threshold H).card +
        (C * Kakeya.realRpowENN (threshold / delta) 1) *
          (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 +
        (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 *
          (C * Kakeya.realRpowENN (threshold / delta) 1) := by
  let badF := F.filter fun point => dist point 0 < threshold
  have hbadF : badF ⊆ F := Finset.filter_subset _ _
  have hbadFirstEq :
      (H.filter fun edge => dist edge.1 0 < threshold) =
        H.filter fun edge => edge.1 ∈ badF := by
    ext edge
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hedge, hdist⟩
      exact ⟨hedge, Finset.mem_filter.mpr
        ⟨(hsupport edge hedge).1, hdist⟩⟩
    · rintro ⟨hedge, hbad⟩
      exact ⟨hedge, (Finset.mem_filter.mp hbad).2⟩
  have hbadFcard :
      (badF.card : ENNReal) ≤
        C * Kakeya.realRpowENN (threshold / delta) 1 := by
    let closed := F.filter fun point => dist point 0 ≤ threshold
    have hsub : badF ⊆ closed := by
      intro point hpoint
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hpoint).1,
          (Finset.mem_filter.mp hpoint).2.le⟩
    calc
      (badF.card : ENNReal) ≤ (closed.card : ENNReal) := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ C * Kakeya.realRpowENN (threshold / delta) 1 := by
        simpa [closed, DiscreteSet.ballCount] using
          hFkt 0 threshold hdeltaThreshold hthresholdOne
  have hFcard :
      F.enncard ≤ C * Kakeya.realRpowENN (1 / delta) 1 :=
    katzTao_unit_ball_card hdelta hdeltaOne hFball hFkt
  have hGcard :
      G.enncard ≤ C * Kakeya.realRpowENN (1 / delta) 1 :=
    katzTao_unit_ball_card hdelta hdeltaOne hGball hGkt
  have hfirstNat := supported_first_bad_card hsupport hbadF
  have hfirst :
      ((H.filter fun edge => dist edge.1 0 < threshold).card : ENNReal) ≤
        (C * Kakeya.realRpowENN (threshold / delta) 1) *
          (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 := by
    rw [hbadFirstEq]
    calc
      ((H.filter fun edge => edge.1 ∈ badF).card : ENNReal)
          ≤ (badF.card : ENNReal) * G.enncard * G.enncard := by
            calc
              ((H.filter fun edge => edge.1 ∈ badF).card : ENNReal)
                  ≤ ((badF.card * G.card * G.card : ℕ) : ENNReal) := by
                    exact_mod_cast hfirstNat
              _ = (badF.card : ENNReal) * G.enncard * G.enncard := by
                    simp [DiscreteSet.enncard, Nat.cast_mul]
      _ ≤ (C * Kakeya.realRpowENN (threshold / delta) 1) *
            (C * Kakeya.realRpowENN (1 / delta) 1) *
            (C * Kakeya.realRpowENN (1 / delta) 1) := by
            gcongr
      _ = (C * Kakeya.realRpowENN (threshold / delta) 1) *
            (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 := by ring
  have hpairs := close_endpoint_pairs_card hGkt
    hdeltaThreshold hthresholdOne
  have hendpointsNat := supported_close_endpoints_card hsupport threshold
  have hendpoints :
      ((H.filter fun edge =>
        dist edge.2.1 edge.2.2 < threshold).card : ENNReal) ≤
        (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 *
          (C * Kakeya.realRpowENN (threshold / delta) 1) := by
    calc
      ((H.filter fun edge =>
        dist edge.2.1 edge.2.2 < threshold).card : ENNReal)
          ≤ F.enncard *
              (((G.product G).filter fun pair =>
                dist pair.1 pair.2 < threshold).card : ENNReal) := by
            calc
              ((H.filter fun edge =>
                dist edge.2.1 edge.2.2 < threshold).card : ENNReal)
                  ≤ ((F.card *
                    ((G.product G).filter fun pair =>
                      dist pair.1 pair.2 < threshold).card : ℕ) : ENNReal) := by
                    exact_mod_cast hendpointsNat
              _ = F.enncard *
                  (((G.product G).filter fun pair =>
                    dist pair.1 pair.2 < threshold).card : ENNReal) := by
                    simp [DiscreteSet.enncard, Nat.cast_mul]
      _ ≤ (C * Kakeya.realRpowENN (1 / delta) 1) *
            (G.enncard *
              (C * Kakeya.realRpowENN (threshold / delta) 1)) := by
            gcongr
      _ ≤ (C * Kakeya.realRpowENN (1 / delta) 1) *
            ((C * Kakeya.realRpowENN (1 / delta) 1) *
              (C * Kakeya.realRpowENN (threshold / delta) 1)) := by
            gcongr
      _ = (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 *
            (C * Kakeya.realRpowENN (threshold / delta) 1) := by ring
  calc
    (H.card : ENNReal)
        ≤ (wz1CommonEndpointGoodEdges threshold H).card +
            (H.filter fun edge => dist edge.1 0 < threshold).card +
            (H.filter fun edge =>
              dist edge.2.1 edge.2.2 < threshold).card :=
          common_endpoint_good_bad_cover_card
    _ ≤ (wz1CommonEndpointGoodEdges threshold H).card +
          (C * Kakeya.realRpowENN (threshold / delta) 1) *
            (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 +
          (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 *
            (C * Kakeya.realRpowENN (threshold / delta) 1) := by
          gcongr

end

end Kakeya.Assouad
