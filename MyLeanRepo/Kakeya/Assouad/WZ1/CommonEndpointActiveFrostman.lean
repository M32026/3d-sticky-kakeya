import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointBadEdgeCount

/-!
# Active-projection cardinality and Frostman normalization

These lemmas isolate the purely finite bridge used after common-endpoint
localization.  A supported graph controls the product of its active
coordinate projections.  An absolute Katz--Tao bound becomes a normalized
Frostman bound once the active class has the required explicit cardinality.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- A supported tripartite graph has at most the full product cardinality. -/
lemma supported_graph_card_le_product
    {A₀ A₁ A₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ A₀ ∧ edge.2.1 ∈ A₁ ∧ edge.2.2 ∈ A₂) :
    (H.card : ENNReal) ≤ A₀.enncard * A₁.enncard * A₂.enncard := by
  let target := A₀.product (A₁.product A₂)
  have hsub : H ⊆ target := by
    intro edge hedge
    have hs := hsupport edge hedge
    exact Finset.mem_product.mpr
      ⟨hs.1, Finset.mem_product.mpr ⟨hs.2.1, hs.2.2⟩⟩
  calc
    (H.card : ENNReal) ≤ (target.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = A₀.enncard * A₁.enncard * A₂.enncard := by
      simp [target, DiscreteSet.enncard, Finset.card_product, Nat.cast_mul]
      ac_rfl

/-- The actual coordinate images of a graph support that graph. -/
lemma active_projection_support
    {H : Finset (Point2 × Point2 × Point2)} :
    ∀ edge ∈ H,
      edge.1 ∈ wz1ActiveTripleProjection H 0 ∧
        edge.2.1 ∈ wz1ActiveTripleProjection H 1 ∧
        edge.2.2 ∈ wz1ActiveTripleProjection H 2 := by
  intro edge hedge
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply Finset.mem_image.mpr
    exact ⟨edge, hedge, by simp [wz1TripleCoordinate]⟩

/-- Edge cardinality is bounded by the product of the three active
coordinate projections. -/
lemma graph_card_le_active_product
    {H : Finset (Point2 × Point2 × Point2)} :
    (H.card : ENNReal) ≤
      (wz1ActiveTripleProjection H 0).enncard *
        (wz1ActiveTripleProjection H 1).enncard *
        (wz1ActiveTripleProjection H 2).enncard :=
  supported_graph_card_le_product active_projection_support

/-- Supported-graph lower bound for the first prescribed vertex class. -/
lemma supported_first_card_lower
    {A₀ A₁ A₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower otherUpper : ENNReal}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ A₀ ∧ edge.2.1 ∈ A₁ ∧ edge.2.2 ∈ A₂)
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirstOther : A₁.enncard ≤ otherUpper)
    (hsecondOther : A₂.enncard ≤ otherUpper) :
    edgeLower ≤ A₀.enncard * otherUpper ^ 2 := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ A₀.enncard * A₁.enncard * A₂.enncard :=
      supported_graph_card_le_product hsupport
    _ ≤ A₀.enncard * otherUpper * otherUpper := by gcongr
    _ = A₀.enncard * otherUpper ^ 2 := by ring

/-- Supported-graph lower bound for the second prescribed vertex class. -/
lemma supported_second_card_lower
    {A₀ A₁ A₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower firstUpper thirdUpper : ENNReal}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ A₀ ∧ edge.2.1 ∈ A₁ ∧ edge.2.2 ∈ A₂)
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirst : A₀.enncard ≤ firstUpper)
    (hthird : A₂.enncard ≤ thirdUpper) :
    edgeLower ≤ firstUpper * A₁.enncard * thirdUpper := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ A₀.enncard * A₁.enncard * A₂.enncard :=
      supported_graph_card_le_product hsupport
    _ ≤ firstUpper * A₁.enncard * thirdUpper := by gcongr

/-- Supported-graph lower bound for the third prescribed vertex class. -/
lemma supported_third_card_lower
    {A₀ A₁ A₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower firstUpper secondUpper : ENNReal}
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ A₀ ∧ edge.2.1 ∈ A₁ ∧ edge.2.2 ∈ A₂)
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirst : A₀.enncard ≤ firstUpper)
    (hsecond : A₁.enncard ≤ secondUpper) :
    edgeLower ≤ firstUpper * secondUpper * A₂.enncard := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ A₀.enncard * A₁.enncard * A₂.enncard :=
      supported_graph_card_le_product hsupport
    _ ≤ firstUpper * secondUpper * A₂.enncard := by gcongr

/-- If the two other active classes have known upper bounds, the first
active class has the corresponding lower bound. -/
lemma active_first_card_lower
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower otherUpper : ENNReal}
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirstOther :
      (wz1ActiveTripleProjection H 1).enncard ≤ otherUpper)
    (hsecondOther :
      (wz1ActiveTripleProjection H 2).enncard ≤ otherUpper) :
    edgeLower ≤
      (wz1ActiveTripleProjection H 0).enncard * otherUpper ^ 2 := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ (wz1ActiveTripleProjection H 0).enncard *
          (wz1ActiveTripleProjection H 1).enncard *
          (wz1ActiveTripleProjection H 2).enncard :=
        graph_card_le_active_product
    _ ≤ (wz1ActiveTripleProjection H 0).enncard *
          otherUpper * otherUpper := by gcongr
    _ = (wz1ActiveTripleProjection H 0).enncard *
          otherUpper ^ 2 := by ring

/-- Symmetric lower bound for the second coordinate projection. -/
lemma active_second_card_lower
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower firstUpper thirdUpper : ENNReal}
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirst : (wz1ActiveTripleProjection H 0).enncard ≤ firstUpper)
    (hthird : (wz1ActiveTripleProjection H 2).enncard ≤ thirdUpper) :
    edgeLower ≤
      firstUpper * (wz1ActiveTripleProjection H 1).enncard * thirdUpper := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ (wz1ActiveTripleProjection H 0).enncard *
          (wz1ActiveTripleProjection H 1).enncard *
          (wz1ActiveTripleProjection H 2).enncard :=
        graph_card_le_active_product
    _ ≤ firstUpper *
          (wz1ActiveTripleProjection H 1).enncard * thirdUpper := by gcongr

/-- Symmetric lower bound for the third coordinate projection. -/
lemma active_third_card_lower
    {H : Finset (Point2 × Point2 × Point2)}
    {edgeLower firstUpper secondUpper : ENNReal}
    (hedge : edgeLower ≤ (H.card : ENNReal))
    (hfirst : (wz1ActiveTripleProjection H 0).enncard ≤ firstUpper)
    (hsecond : (wz1ActiveTripleProjection H 1).enncard ≤ secondUpper) :
    edgeLower ≤
      firstUpper * secondUpper *
        (wz1ActiveTripleProjection H 2).enncard := by
  calc
    edgeLower ≤ (H.card : ENNReal) := hedge
    _ ≤ (wz1ActiveTripleProjection H 0).enncard *
          (wz1ActiveTripleProjection H 1).enncard *
          (wz1ActiveTripleProjection H 2).enncard :=
        graph_card_le_active_product
    _ ≤ firstUpper * secondUpper *
          (wz1ActiveTripleProjection H 2).enncard := by gcongr

/-- Normalize an absolute one-dimensional Katz--Tao estimate by an explicit
cardinality coefficient inequality. -/
lemma DiscreteSet.IsKatzTao.toFrostman_of_coefficient
    {A : DiscreteSet 2}
    {delta Cabs Cnorm : ℝ}
    (hKT : A.IsKatzTao delta 1 (ENNReal.ofReal Cabs))
    (hdelta : 0 < delta)
    (hcoefficient :
      ENNReal.ofReal Cabs * ENNReal.ofReal (1 / delta) ≤
        ENNReal.ofReal Cnorm * A.enncard) :
    A.IsFrostman delta 1 (ENNReal.ofReal Cnorm) := by
  intro center radius hdeltaRadius hradiusOne
  have hradius : 0 < radius := hdelta.trans_le hdeltaRadius
  have hraw := hKT center radius hdeltaRadius hradiusOne
  have hratio :
      Kakeya.realRpowENN (radius / delta) 1 =
        ENNReal.ofReal radius * ENNReal.ofReal (1 / delta) := by
    simp only [Kakeya.realRpowENN]
    rw [show radius / delta = radius * (1 / delta) by ring]
    rw [show Real.rpow (radius * (1 / delta)) 1 =
      radius * (1 / delta) from Real.rpow_one _]
    rw [ENNReal.ofReal_mul hradius.le]
  calc
    A.ballCount center radius
        ≤ ENNReal.ofReal Cabs *
            Kakeya.realRpowENN (radius / delta) 1 := hraw
    _ = ENNReal.ofReal radius *
          (ENNReal.ofReal Cabs * ENNReal.ofReal (1 / delta)) := by
          rw [hratio]
          ac_rfl
    _ ≤ ENNReal.ofReal radius *
          (ENNReal.ofReal Cnorm * A.enncard) := by gcongr
    _ = ENNReal.ofReal Cnorm *
          Kakeya.realRpowENN radius 1 * A.enncard := by
          simp [Kakeya.realRpowENN, Real.rpow_one]
          ac_rfl

/-- Cancel the two ambient-card upper bounds after a cubic power budget. -/
lemma coefficient_of_active_cubic
    {edge upper normalized card : ENNReal}
    (hupperZero : upper ≠ 0) (hupperTop : upper ≠ ⊤)
    (hactive : edge ≤ card * upper ^ 2)
    (hcubic : upper ^ 3 ≤ normalized * edge) :
    upper ≤ normalized * card := by
  have hupperSqZero : upper ^ 2 ≠ 0 := pow_ne_zero _ hupperZero
  have hupperSqTop : upper ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hupperTop
  apply (ENNReal.mul_le_mul_iff_left hupperSqZero hupperSqTop).1
  calc
    upper * upper ^ 2 = upper ^ 3 := by ring
    _ ≤ normalized * edge := hcubic
    _ ≤ normalized * (card * upper ^ 2) := by gcongr
    _ = (normalized * card) * upper ^ 2 := by ring

/-- Convert the edge lower bound and three vertex-cardinality upper bounds
into the uniform density produced by Lemma 37. -/
lemma refinement_density_of_power_budget
    {density epsilon edge graphCard upper cardF cardG₁ cardG₂ : ENNReal}
    (_hgraphTop : graphCard ≠ ⊤)
    (hcardsZero : cardF * cardG₁ * cardG₂ ≠ 0)
    (hcardsTop : cardF * cardG₁ * cardG₂ ≠ ⊤)
    (hF : cardF ≤ upper) (hG₁ : cardG₁ ≤ upper)
    (hG₂ : cardG₂ ≤ upper)
    (hedge : edge ≤ graphCard)
    (hpower : 8 * density * upper ^ 3 ≤ epsilon * edge) :
    density ≤ (epsilon / 8) *
      (graphCard / (cardF * cardG₁ * cardG₂)) := by
  let product := cardF * cardG₁ * cardG₂
  have hproduct : product ≤ upper ^ 3 := by
    dsimp only [product]
    calc
      cardF * cardG₁ * cardG₂ ≤ upper * upper * upper := by gcongr
      _ = upper ^ 3 := by ring
  have hdivided : density * upper ^ 3 ≤ (epsilon / 8) * edge := by
    have hraw : density * upper ^ 3 ≤ (epsilon * edge) / 8 := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
        (Or.inl (by norm_num))).2
      calc
        density * upper ^ 3 * 8 = 8 * density * upper ^ 3 := by ring
        _ ≤ epsilon * edge := hpower
    calc
      density * upper ^ 3 ≤ (epsilon * edge) / 8 := hraw
      _ = (epsilon / 8) * edge := by
        simp [div_eq_mul_inv]
        ring
  have hproductBound :
      density * product ≤ (epsilon / 8) * graphCard := by
    calc
      density * product ≤ density * upper ^ 3 := by gcongr
      _ ≤ (epsilon / 8) * edge := hdivided
      _ ≤ (epsilon / 8) * graphCard := by gcongr
  have hraw : density ≤ ((epsilon / 8) * graphCard) / product := by
    apply (ENNReal.le_div_iff_mul_le
      (a := density) (b := product)
      (c := (epsilon / 8) * graphCard)
      (Or.inl (by simpa [product] using hcardsZero))
      (Or.inl (by simpa [product] using hcardsTop))).2
    simpa [product] using hproductBound
  calc
    density ≤ ((epsilon / 8) * graphCard) / product := hraw
    _ = (epsilon / 8) * (graphCard / product) := by
      simp [div_eq_mul_inv]
      ring

end

end Kakeya.Assouad
