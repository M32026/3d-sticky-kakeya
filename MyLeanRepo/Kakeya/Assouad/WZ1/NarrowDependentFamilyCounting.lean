import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedSecondaryStatements
import Mathlib.Data.Finset.Sigma

/-!
# Counting dependent narrow incidence families

The remaining narrow leaves use a finite outer family together with a
different literal graph fiber over each outer point.  The dependent sum keeps
the outer anchor in the index, so cardinality multiplication is never inferred
from a Cartesian set of unsupported mixed edges.
-/

namespace Kakeya.Assouad

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-- The cardinality of a dependent finite family is the sum of its fiber
cardinalities. -/
lemma narrow_dependent_family_card
    {index : Type*} {fiberType : index → Type*}
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current)) :
    (outer.sigma fiber).card =
      ∑ current ∈ outer, (fiber current).card := by
  change
    Multiset.card
        (Multiset.sigma outer.1 fun current =>
          (fiber current).1) =
      _
  rw [Multiset.card_sigma]
  simp

/-- A uniform lower bound for each dependent fiber multiplies by the number
of outer anchors. -/
lemma narrow_dependent_family_card_lower
    {index : Type*} {fiberType : index → Type*}
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current))
    (threshold : ENNReal)
    (fiber_lower :
      ∀ current ∈ outer,
        threshold ≤ (fiber current).card) :
    threshold * (outer.card : ENNReal) ≤
      ((outer.sigma fiber).card : ENNReal) := by
  rw [narrow_dependent_family_card outer fiber]
  rw [Nat.cast_sum]
  calc
    threshold * (outer.card : ENNReal) =
        ∑ current ∈ outer, threshold := by
      simp [mul_comm]
    _ ≤
        ∑ current ∈ outer,
          ((fiber current).card : ENNReal) := by
      exact Finset.sum_le_sum fiber_lower

/--
If the literal edge attached to a dependent pair preserves its outer index
and is injective inside each fiber, then flattening the family to edges loses
no cardinality.
-/
lemma narrow_dependent_edge_image_card
    {index target : Type*} {fiberType : index → Type*}
    [DecidableEq target]
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current))
    (edge : (Σ current, fiberType current) → index × target)
    (outer_eq :
      ∀ pair ∈ outer.sigma fiber,
        (edge pair).1 = pair.1)
    (fiber_injective :
      ∀ current,
        Set.InjOn
          (fun value => edge ⟨current, value⟩)
          (fiber current : Set (fiberType current))) :
    ((outer.sigma fiber).image edge).card =
      (outer.sigma fiber).card := by
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond hedge
  have hindex : first.1 = second.1 := by
    rw [← outer_eq first hfirst,
      ← outer_eq second hsecond, hedge]
  cases first with
  | mk firstIndex firstValue =>
    cases second with
    | mk secondIndex secondValue =>
      simp only at hindex
      subst secondIndex
      have hvalue : firstValue = secondValue :=
        fiber_injective firstIndex
          (Finset.mem_sigma.mp hfirst).2
          (Finset.mem_sigma.mp hsecond).2 hedge
      subst secondValue
      rfl

/--
The outer coordinate may be encoded by an injective anchor value rather than
stored literally in the edge.  This is the form used when distinct outer
first vertices label literal edge fibers.
-/
lemma narrow_dependent_edge_image_card_of_outer_key
    {index key target : Type*} {fiberType : index → Type*}
    [DecidableEq target]
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current))
    (outerKey : index → key)
    (edge : (Σ current, fiberType current) → key × target)
    (outerKey_injective :
      Set.InjOn outerKey (outer : Set index))
    (outer_eq :
      ∀ pair ∈ outer.sigma fiber,
        (edge pair).1 = outerKey pair.1)
    (fiber_injective :
      ∀ current,
        Set.InjOn
          (fun value => edge ⟨current, value⟩)
          (fiber current : Set (fiberType current))) :
    ((outer.sigma fiber).image edge).card =
      (outer.sigma fiber).card := by
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond hedge
  have hkey :
      outerKey first.1 = outerKey second.1 := by
    rw [← outer_eq first hfirst,
      ← outer_eq second hsecond, hedge]
  have hindex : first.1 = second.1 :=
    outerKey_injective
      (Finset.mem_sigma.mp hfirst).1
      (Finset.mem_sigma.mp hsecond).1 hkey
  cases first with
  | mk firstIndex firstValue =>
    cases second with
    | mk secondIndex secondValue =>
      simp only at hindex
      subst secondIndex
      have hvalue : firstValue = secondValue :=
        fiber_injective firstIndex
          (Finset.mem_sigma.mp hfirst).2
          (Finset.mem_sigma.mp hsecond).2 hedge
      subst secondValue
      rfl

/--
General outer-key version: the anchor may be recovered from any projection of
the encoded target.  This covers nested third-coordinate families, where the
outer key is the third coordinate of a literal edge.
-/
lemma narrow_dependent_image_card_of_outer_key
    {index key target : Type*} {fiberType : index → Type*}
    [DecidableEq target]
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current))
    (outerKey : index → key)
    (value : (Σ current, fiberType current) → target)
    (valueKey : target → key)
    (outerKey_injective :
      Set.InjOn outerKey (outer : Set index))
    (outer_eq :
      ∀ pair ∈ outer.sigma fiber,
        valueKey (value pair) = outerKey pair.1)
    (fiber_injective :
      ∀ current,
        Set.InjOn
          (fun element => value ⟨current, element⟩)
          (fiber current : Set (fiberType current))) :
    ((outer.sigma fiber).image value).card =
      (outer.sigma fiber).card := by
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond hvalue
  have hkey :
      outerKey first.1 = outerKey second.1 := by
    rw [← outer_eq first hfirst,
      ← outer_eq second hsecond, hvalue]
  have hindex : first.1 = second.1 :=
    outerKey_injective
      (Finset.mem_sigma.mp hfirst).1
      (Finset.mem_sigma.mp hsecond).1 hkey
  cases first with
  | mk firstIndex firstValue =>
    cases second with
    | mk secondIndex secondValue =>
      simp only at hindex
      subst secondIndex
      have hvalueEq : firstValue = secondValue :=
        fiber_injective firstIndex
          (Finset.mem_sigma.mp hfirst).2
          (Finset.mem_sigma.mp hsecond).2 hvalue
      subst secondValue
      rfl

/-- Every value in the flattened image has a dependent source witness, so a
pointwise literal-edge proof transports to the whole image. -/
lemma narrow_dependent_image_subset
    {index target : Type*} {fiberType : index → Type*}
    [DecidableEq target]
    (outer : Finset index)
    (fiber : ∀ current, Finset (fiberType current))
    (value : (Σ current, fiberType current) → target)
    (targetSet : Finset target)
    (value_mem :
      ∀ pair ∈ outer.sigma fiber,
        value pair ∈ targetSet) :
    (outer.sigma fiber).image value ⊆ targetSet := by
  intro output houtput
  rcases Finset.mem_image.mp houtput with
    ⟨pair, hpair, rfl⟩
  exact value_mem pair hpair

/--
Literal outer-first/secondary-`G₁` incidences in the two-center first-escape
branch.  The outer first coordinate makes the edge encoding injective across
different fibers, while the inner second coordinate makes it injective inside
one fiber.
-/
theorem wz1_narrow_first_escape_two_center_literal_g1_edges
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (escapeData :
      WZ1NarrowFirstEscapeSecondaryFirstEscapeData
        primary family)
    (centerData :
      WZ1NarrowFirstEscapeCenterConcentratedData
        primary family escapeData)
    (firstCenterData :
      WZ1NarrowFamilyCenterConcentratedData
        centerData.points
        (fun first =>
          (family.package first.1 first.2).obstruction.firstDotCenter)
        delta epsilon eta parameters.workingLambda) :
    ∃ edges : Finset (Point2 × Point2 × Point2),
      (2 * Kakeya.realRpowENN delta (epsilon - 1)) *
          (firstCenterData.points.card : ENNReal) ≤
        (edges.card : ENNReal) ∧
      edges ⊆ data.refinedH ∧
      ∀ edge ∈ edges,
        |inner ℝ edge.1 (edge.2.1 - edge.2.2) -
            centerData.center| ≤
          4 * delta := by
  let source := firstCenterData.points
  let packageAt
      (first : {point // point ∈ wz1NarrowFirstEscapedPoints primary}) :=
    family.package first.1 first.2
  let fiber :
      ∀ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
        Finset Point2 :=
    fun first => (packageAt first).concentration.points
  let edge :
      (Σ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
          Point2) →
        Point2 × Point2 × Point2 :=
    fun pair => (pair.1.1, pair.2, primary.third)
  let edges := (source.sigma fiber).image edge
  have hsourceInjective :
      Set.InjOn
        (fun first :
          {point // point ∈ wz1NarrowFirstEscapedPoints primary} =>
            first.1)
        (source : Set
          {point // point ∈ wz1NarrowFirstEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hedgeCard :
      edges.card = (source.sigma fiber).card := by
    simpa [edges] using
      narrow_dependent_image_card_of_outer_key
        source fiber
        (fun first => first.1) edge
        (fun current => current.1)
        hsourceInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro first
          intro firstSecond _ secondSecond _ heq
          simpa [edge] using
            congrArg (fun current => current.2.1) heq)
  have hsourceCard :
      (2 * Kakeya.realRpowENN delta (epsilon - 1)) *
          (source.card : ENNReal) ≤
        ((source.sigma fiber).card : ENNReal) := by
    exact
      narrow_dependent_family_card_lower
        source fiber
        (2 * Kakeya.realRpowENN delta (epsilon - 1))
        (by
          intro first _hfirst
          exact (packageAt first).concentration.card_lower)
  refine ⟨edges, ?_, ?_, ?_⟩
  · rw [hedgeCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hsecond := (Finset.mem_sigma.mp hpair).2
    have hactual :=
      (packageAt pair.1).concentration.actual_edges
        pair.2 hsecond
    have hanchor := (packageAt pair.1).anchored
    simpa [edge, packageAt, hanchor.1, hanchor.2] using hactual
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hsource := (Finset.mem_sigma.mp hpair).1
    have hsecond := (Finset.mem_sigma.mp hpair).2
    have hdot :=
      (packageAt pair.1).concentration.dot_concentrated
        pair.2 hsecond
    have hcenter :=
      centerData.concentrated pair.1
        (firstCenterData.points_subset hsource)
    have hanchor := (packageAt pair.1).anchored
    have hdot' :
        |inner ℝ pair.1.1 (pair.2 - primary.third) -
            (packageAt pair.1).concentration.dotCenter| ≤
          delta := by
      simpa [packageAt, hanchor.1, hanchor.2] using hdot
    have htriangle :
        |inner ℝ pair.1.1 (pair.2 - primary.third) -
            centerData.center| ≤
          |inner ℝ pair.1.1 (pair.2 - primary.third) -
              (packageAt pair.1).concentration.dotCenter| +
            |(packageAt pair.1).concentration.dotCenter -
              centerData.center| := by
      have heq :
          inner ℝ pair.1.1 (pair.2 - primary.third) -
              centerData.center =
            (inner ℝ pair.1.1 (pair.2 - primary.third) -
                (packageAt pair.1).concentration.dotCenter) +
              ((packageAt pair.1).concentration.dotCenter -
                centerData.center) := by
        ring
      rw [heq]
      exact abs_add_le _ _
    simpa [edge] using htriangle.trans (by linarith)

/-- Restrict the two-center literal `G₁` edge family to any supplied outer
subfamily. -/
theorem wz1_narrow_first_escape_two_center_literal_g1_edges_restrict
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (outer :
      Finset
        {first // first ∈ wz1NarrowFirstEscapedPoints primary}) :
    ∃ edges : Finset (Point2 × Point2 × Point2),
      (2 * Kakeya.realRpowENN delta (epsilon - 1)) *
          (outer.card : ENNReal) ≤
        (edges.card : ENNReal) ∧
      edges ⊆ data.refinedH := by
  let packageAt
      (first : {point // point ∈ wz1NarrowFirstEscapedPoints primary}) :=
    family.package first.1 first.2
  let fiber :
      ∀ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
        Finset Point2 :=
    fun first => (packageAt first).concentration.points
  let edge :
      (Σ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
          Point2) →
        Point2 × Point2 × Point2 :=
    fun pair => (pair.1.1, pair.2, primary.third)
  let edges := (outer.sigma fiber).image edge
  have houterInjective :
      Set.InjOn
        (fun first :
          {point // point ∈ wz1NarrowFirstEscapedPoints primary} =>
            first.1)
        (outer : Set
          {point // point ∈ wz1NarrowFirstEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hedgeCard :
      edges.card = (outer.sigma fiber).card := by
    simpa [edges] using
      narrow_dependent_image_card_of_outer_key
        outer fiber
        (fun first => first.1) edge
        (fun current => current.1)
        houterInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro first
          intro firstSecond _ secondSecond _ heq
          simpa [edge] using
            congrArg (fun current => current.2.1) heq)
  have hsourceCard :
      (2 * Kakeya.realRpowENN delta (epsilon - 1)) *
          (outer.card : ENNReal) ≤
        ((outer.sigma fiber).card : ENNReal) :=
    narrow_dependent_family_card_lower
      outer fiber
      (2 * Kakeya.realRpowENN delta (epsilon - 1))
      (by
        intro first _hfirst
        exact (packageAt first).concentration.card_lower)
  refine ⟨edges, ?_, ?_⟩
  · rw [hedgeCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hsecond := (Finset.mem_sigma.mp hpair).2
    have hactual :=
      (packageAt pair.1).concentration.actual_edges
        pair.2 hsecond
    have hanchor := (packageAt pair.1).anchored
    simpa [edge, packageAt, hanchor.1, hanchor.2] using hactual

/--
Literal outer-first/escaped-secondary-third incidences in the aligned
first-family branch.  Distinct outer first vertices and distinct inner third
vertices give distinct literal graph edges.
-/
theorem wz1_narrow_first_aligned_literal_escaped_third_edges
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (alignedData :
      WZ1NarrowFirstEscapeSecondaryFirstAlignedData
        primary family)
    (third_escape :
      ∀ first ∈ alignedData.points,
        ¬ WZ1NarrowThirdFiberAligned
          (family.package first.1 first.2).obstruction)
    (centerData :
      WZ1NarrowFamilyCenterConcentratedData
        alignedData.points
        (fun first =>
          (family.package first.1 first.2).obstruction.thirdDotCenter)
        delta epsilon eta parameters.workingLambda) :
    ∃ edges : Finset (Point2 × Point2 × Point2),
      Kakeya.realRpowENN delta (epsilon - 1) *
          (centerData.points.card : ENNReal) ≤
        (edges.card : ENNReal) ∧
      edges ⊆ data.refinedH ∧
      ∀ edge ∈ edges,
        |inner ℝ edge.1 (edge.2.1 - edge.2.2) -
            centerData.center| ≤
          4 * delta := by
  let source := centerData.points
  let packageAt
      (first : {point // point ∈ wz1NarrowFirstEscapedPoints primary}) :=
    family.package first.1 first.2
  let fiber :
      ∀ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
        Finset Point2 :=
    fun first =>
      wz1NarrowThirdEscapedPoints (packageAt first).obstruction
  let edge :
      (Σ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
          Point2) →
        Point2 × Point2 × Point2 :=
    fun pair =>
      (pair.1.1, (packageAt pair.1).obstruction.second, pair.2)
  let edges := (source.sigma fiber).image edge
  have hsourceInjective :
      Set.InjOn
        (fun first :
          {point // point ∈ wz1NarrowFirstEscapedPoints primary} =>
            first.1)
        (source : Set
          {point // point ∈ wz1NarrowFirstEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hedgeCard :
      edges.card = (source.sigma fiber).card := by
    simpa [edges] using
      narrow_dependent_image_card_of_outer_key
        source fiber
        (fun first => first.1) edge
        (fun current => current.1)
        hsourceInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro first
          intro firstThird _ secondThird _ heq
          simpa [edge] using
            congrArg (fun current => current.2.2) heq)
  have hsourceCard :
      Kakeya.realRpowENN delta (epsilon - 1) *
          (source.card : ENNReal) ≤
        ((source.sigma fiber).card : ENNReal) := by
    exact
      narrow_dependent_family_card_lower
        source fiber
        (Kakeya.realRpowENN delta (epsilon - 1))
        (by
          intro first hfirst
          exact
            wz1Narrow_thirdEscapedPoints_card
              (packageAt first).obstruction
              (third_escape first
                (centerData.points_subset hfirst)))
  refine ⟨edges, ?_, ?_, ?_⟩
  · rw [hedgeCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hthird := (Finset.mem_sigma.mp hpair).2
    have hactual :=
      wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hthird
    have hanchor := (packageAt pair.1).anchored
    simpa [edge, packageAt, hanchor.1] using hactual.2.1
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hsource := (Finset.mem_sigma.mp hpair).1
    have hthird := (Finset.mem_sigma.mp hpair).2
    have hactual :=
      wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hthird
    have hdot :=
      (packageAt pair.1).obstruction.thirdPoints_dot_concentrated
        pair.2 hactual.1
    have hcenter :=
      centerData.concentrated pair.1 hsource
    have hanchor := (packageAt pair.1).anchored
    have hdot' :
        |inner ℝ pair.1.1
              ((packageAt pair.1).obstruction.second - pair.2) -
            (packageAt pair.1).obstruction.thirdDotCenter| ≤
          delta := by
      simpa [packageAt, hanchor.1] using hdot
    have htriangle :
        |inner ℝ pair.1.1
              ((packageAt pair.1).obstruction.second - pair.2) -
            centerData.center| ≤
          |inner ℝ pair.1.1
                ((packageAt pair.1).obstruction.second - pair.2) -
              (packageAt pair.1).obstruction.thirdDotCenter| +
            |(packageAt pair.1).obstruction.thirdDotCenter -
              centerData.center| := by
      have heq :
          inner ℝ pair.1.1
                ((packageAt pair.1).obstruction.second - pair.2) -
              centerData.center =
            (inner ℝ pair.1.1
                ((packageAt pair.1).obstruction.second - pair.2) -
                (packageAt pair.1).obstruction.thirdDotCenter) +
              ((packageAt pair.1).obstruction.thirdDotCenter -
                centerData.center) := by
        ring
      rw [heq]
      exact abs_add_le _ _
    simpa [edge] using htriangle.trans (by linarith)

/-- Restrict the aligned-first escaped-third literal edge family to a supplied
outer subfamily. -/
theorem wz1_narrow_first_aligned_literal_escaped_third_edges_restrict
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (outer :
      Finset
        {first // first ∈ wz1NarrowFirstEscapedPoints primary})
    (outer_subset :
      ∀ first ∈ outer,
        ¬ WZ1NarrowThirdFiberAligned
          (family.package first.1 first.2).obstruction) :
    ∃ edges : Finset (Point2 × Point2 × Point2),
      Kakeya.realRpowENN delta (epsilon - 1) *
          (outer.card : ENNReal) ≤
        (edges.card : ENNReal) ∧
      edges ⊆ data.refinedH := by
  let packageAt
      (first : {point // point ∈ wz1NarrowFirstEscapedPoints primary}) :=
    family.package first.1 first.2
  let fiber :
      ∀ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
        Finset Point2 :=
    fun first =>
      wz1NarrowThirdEscapedPoints (packageAt first).obstruction
  let edge :
      (Σ _first :
        {point // point ∈ wz1NarrowFirstEscapedPoints primary},
          Point2) →
        Point2 × Point2 × Point2 :=
    fun pair =>
      (pair.1.1, (packageAt pair.1).obstruction.second, pair.2)
  let edges := (outer.sigma fiber).image edge
  have houterInjective :
      Set.InjOn
        (fun first :
          {point // point ∈ wz1NarrowFirstEscapedPoints primary} =>
            first.1)
        (outer : Set
          {point // point ∈ wz1NarrowFirstEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hedgeCard :
      edges.card = (outer.sigma fiber).card := by
    simpa [edges] using
      narrow_dependent_image_card_of_outer_key
        outer fiber
        (fun first => first.1) edge
        (fun current => current.1)
        houterInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro first
          intro firstThird _ secondThird _ heq
          simpa [edge] using
            congrArg (fun current => current.2.2) heq)
  have hsourceCard :
      Kakeya.realRpowENN delta (epsilon - 1) *
          (outer.card : ENNReal) ≤
        ((outer.sigma fiber).card : ENNReal) :=
    narrow_dependent_family_card_lower
      outer fiber
      (Kakeya.realRpowENN delta (epsilon - 1))
      (by
        intro first hfirst
        exact
          wz1Narrow_thirdEscapedPoints_card
            (packageAt first).obstruction
            (outer_subset first hfirst))
  refine ⟨edges, ?_, ?_⟩
  · rw [hedgeCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hthird := (Finset.mem_sigma.mp hpair).2
    have hactual :=
      wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hthird
    have hanchor := (packageAt pair.1).anchored
    simpa [edge, packageAt, hanchor.1] using hactual.2.1

/--
Coupled literal incidences in the primary-third-escape branch.

For each outer escaped primary third point and each escaped third point of its
secondary obstruction, the first edge records the outer anchor and the second
edge records the inner escaped point.  The pair of edges is therefore
injective in both dependent coordinates, even though the inner edge alone
does not remember the outer third point.
-/
theorem wz1_narrow_third_aligned_literal_nested_third_incidences
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowThirdEscapeSecondaryFamily primary)
    (secondary_third_escape :
      ∀ third hthird,
        ¬ WZ1NarrowThirdFiberAligned
          (family.package third hthird).obstruction)
    (centerData :
      WZ1NarrowFamilyCenterConcentratedData
        ((wz1NarrowThirdEscapedPoints primary).attach)
        (fun third =>
          (family.package third.1 third.2).obstruction.thirdDotCenter)
        delta epsilon eta parameters.workingLambda) :
    ∃ incidences :
        Finset
          ((Point2 × Point2 × Point2) ×
            (Point2 × Point2 × Point2)),
      Kakeya.realRpowENN delta (epsilon - 1) *
          (centerData.points.card : ENNReal) ≤
        (incidences.card : ENNReal) ∧
      (∀ incidence ∈ incidences,
        incidence.1 ∈ data.refinedH ∧
          incidence.2 ∈ data.refinedH) ∧
      ∀ incidence ∈ incidences,
        |inner ℝ incidence.2.1
              (incidence.2.2.1 - incidence.2.2.2) -
            centerData.center| ≤
          4 * delta := by
  let source := centerData.points
  let packageAt
      (third : {point // point ∈ wz1NarrowThirdEscapedPoints primary}) :=
    family.package third.1 third.2
  let fiber :
      ∀ _third :
        {point // point ∈ wz1NarrowThirdEscapedPoints primary},
        Finset Point2 :=
    fun third =>
      wz1NarrowThirdEscapedPoints (packageAt third).obstruction
  let incidence :
      (Σ _third :
        {point // point ∈ wz1NarrowThirdEscapedPoints primary},
          Point2) →
        (Point2 × Point2 × Point2) ×
          (Point2 × Point2 × Point2) :=
    fun pair =>
      ((concentration.first,
          (packageAt pair.1).obstruction.second,
          pair.1.1),
        (concentration.first,
          (packageAt pair.1).obstruction.second,
          pair.2))
  let incidences := (source.sigma fiber).image incidence
  have hsourceInjective :
      Set.InjOn
        (fun third :
          {point // point ∈ wz1NarrowThirdEscapedPoints primary} =>
            third.1)
        (source : Set
          {point // point ∈ wz1NarrowThirdEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hincidenceCard :
      incidences.card = (source.sigma fiber).card := by
    simpa [incidences] using
      narrow_dependent_image_card_of_outer_key
        source fiber
        (fun third => third.1) incidence
        (fun current => current.1.2.2)
        hsourceInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro third
          intro firstInner _ secondInner _ heq
          simpa [incidence] using
            congrArg (fun current => current.2.2.2) heq)
  have hsourceCard :
      Kakeya.realRpowENN delta (epsilon - 1) *
          (source.card : ENNReal) ≤
        ((source.sigma fiber).card : ENNReal) := by
    exact
      narrow_dependent_family_card_lower
        source fiber
        (Kakeya.realRpowENN delta (epsilon - 1))
        (by
          intro third hthird
          exact
            wz1Narrow_thirdEscapedPoints_card
              (packageAt third).obstruction
              (secondary_third_escape third.1 third.2))
  refine ⟨incidences, ?_, ?_, ?_⟩
  · rw [hincidenceCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have houter := (Finset.mem_sigma.mp hpair).1
    have hinner := (Finset.mem_sigma.mp hpair).2
    have hanchorEdge :=
      (packageAt pair.1).concentration.actual_edges
        (packageAt pair.1).obstruction.second
        (packageAt pair.1).obstruction.second_mem
    have hinnerEdge :=
      (wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hinner).2.1
    have hanchor := (packageAt pair.1).anchored
    constructor
    · simpa [incidence, packageAt, hanchor.1, hanchor.2] using
        hanchorEdge
    · simpa [incidence, packageAt, hanchor.1] using hinnerEdge
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have houter := (Finset.mem_sigma.mp hpair).1
    have hinner := (Finset.mem_sigma.mp hpair).2
    have hinnerActual :=
      wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hinner
    have hdot :=
      (packageAt pair.1).obstruction.thirdPoints_dot_concentrated
        pair.2 hinnerActual.1
    have hcenter :=
      centerData.concentrated pair.1 houter
    have hanchor := (packageAt pair.1).anchored
    have hdot' :
        |inner ℝ concentration.first
              ((packageAt pair.1).obstruction.second - pair.2) -
            (packageAt pair.1).obstruction.thirdDotCenter| ≤
          delta := by
      simpa [packageAt, hanchor.1] using hdot
    have htriangle :
        |inner ℝ concentration.first
              ((packageAt pair.1).obstruction.second - pair.2) -
            centerData.center| ≤
          |inner ℝ concentration.first
                ((packageAt pair.1).obstruction.second - pair.2) -
              (packageAt pair.1).obstruction.thirdDotCenter| +
            |(packageAt pair.1).obstruction.thirdDotCenter -
              centerData.center| := by
      have heq :
          inner ℝ concentration.first
                ((packageAt pair.1).obstruction.second - pair.2) -
              centerData.center =
            (inner ℝ concentration.first
                ((packageAt pair.1).obstruction.second - pair.2) -
                (packageAt pair.1).obstruction.thirdDotCenter) +
              ((packageAt pair.1).obstruction.thirdDotCenter -
                centerData.center) := by
        ring
      rw [heq]
      exact abs_add_le _ _
    simpa [incidence] using htriangle.trans (by linarith)

/-- Restrict the nested-third coupled incidence family to a supplied outer
subfamily. -/
theorem wz1_narrow_third_aligned_literal_nested_third_incidences_restrict
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowThirdEscapeSecondaryFamily primary)
    (outer :
      Finset
        {third // third ∈ wz1NarrowThirdEscapedPoints primary})
    (outer_escape :
      ∀ third ∈ outer,
        ¬ WZ1NarrowThirdFiberAligned
          (family.package third.1 third.2).obstruction) :
    ∃ incidences :
        Finset
          ((Point2 × Point2 × Point2) ×
            (Point2 × Point2 × Point2)),
      Kakeya.realRpowENN delta (epsilon - 1) *
          (outer.card : ENNReal) ≤
        (incidences.card : ENNReal) ∧
      ∀ incidence ∈ incidences,
        incidence.1 ∈ data.refinedH ∧
          incidence.2 ∈ data.refinedH := by
  let packageAt
      (third : {point // point ∈ wz1NarrowThirdEscapedPoints primary}) :=
    family.package third.1 third.2
  let fiber :
      ∀ _third :
        {point // point ∈ wz1NarrowThirdEscapedPoints primary},
        Finset Point2 :=
    fun third =>
      wz1NarrowThirdEscapedPoints (packageAt third).obstruction
  let incidence :
      (Σ _third :
        {point // point ∈ wz1NarrowThirdEscapedPoints primary},
          Point2) →
        (Point2 × Point2 × Point2) ×
          (Point2 × Point2 × Point2) :=
    fun pair =>
      ((concentration.first,
          (packageAt pair.1).obstruction.second,
          pair.1.1),
        (concentration.first,
          (packageAt pair.1).obstruction.second,
          pair.2))
  let incidences := (outer.sigma fiber).image incidence
  have houterInjective :
      Set.InjOn
        (fun third :
          {point // point ∈ wz1NarrowThirdEscapedPoints primary} =>
            third.1)
        (outer : Set
          {point // point ∈ wz1NarrowThirdEscapedPoints primary}) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hincidenceCard :
      incidences.card = (outer.sigma fiber).card := by
    simpa [incidences] using
      narrow_dependent_image_card_of_outer_key
        outer fiber
        (fun third => third.1) incidence
        (fun current => current.1.2.2)
        houterInjective
        (by
          intro pair _hpair
          rfl)
        (by
          intro third
          intro firstInner _ secondInner _ heq
          simpa [incidence] using
            congrArg (fun current => current.2.2.2) heq)
  have hsourceCard :
      Kakeya.realRpowENN delta (epsilon - 1) *
          (outer.card : ENNReal) ≤
        ((outer.sigma fiber).card : ENNReal) :=
    narrow_dependent_family_card_lower
      outer fiber
      (Kakeya.realRpowENN delta (epsilon - 1))
      (by
        intro third hthird
        exact
          wz1Narrow_thirdEscapedPoints_card
            (packageAt third).obstruction
            (outer_escape third hthird))
  refine ⟨incidences, ?_, ?_⟩
  · rw [hincidenceCard]
    exact hsourceCard
  · intro current hcurrent
    rcases Finset.mem_image.mp hcurrent with
      ⟨pair, hpair, rfl⟩
    have hinner := (Finset.mem_sigma.mp hpair).2
    have hanchorEdge :=
      (packageAt pair.1).concentration.actual_edges
        (packageAt pair.1).obstruction.second
        (packageAt pair.1).obstruction.second_mem
    have hinnerEdge :=
      (wz1Narrow_thirdEscapedPoints_actual
        (packageAt pair.1).obstruction hinner).2.1
    have hanchor := (packageAt pair.1).anchored
    constructor
    · simpa [incidence, packageAt, hanchor.1, hanchor.2] using
        hanchorEdge
    · simpa [incidence, packageAt, hanchor.1] using hinnerEdge

end

end Kakeya.Assouad
