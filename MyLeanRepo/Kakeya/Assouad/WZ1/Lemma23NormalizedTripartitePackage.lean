import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualTripartitePackage

/-!
# Paper-normalized tripartite package for WZ1 Lemma 23

Theorem 22 is applied at scale `sqrt rho`.  The paper therefore rescales the
height-graph vertex by `rho^(-1/2)` while leaving the two local-graph vertices
unchanged.  This module performs that exact finite normalization.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Rescale only the first vertex of a tripartite edge. -/
def wz1Lemma23NormalizeEdge
    (rho : ℝ) (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  ((1 / Real.sqrt rho) • edge.1, edge.2.1, edge.2.2)

/-- Normalized image of an actual Lemma 23 tripartite graph. -/
def wz1Lemma23NormalizedEdges
    (rho : ℝ) (H : Finset (Point2 × Point2 × Point2)) :
    Finset (Point2 × Point2 × Point2) :=
  H.image (wz1Lemma23NormalizeEdge rho)

/-- The normalized first vertex class. -/
def wz1Lemma23NormalizedFirstVertices
    (rho : ℝ) (F : DiscreteSet 2) : DiscreteSet 2 :=
  F.image fun point => (1 / Real.sqrt rho) • point

/-- Normalize the translated snapped base-slice set by `rho^(-1/2)`. -/
def wz1Lemma23NormalizedBaseValues
    (rho : ℝ) (values : Finset ℝ) : Finset ℝ :=
  values.image fun value => value / Real.sqrt rho

/--
The paper-normalized actual graph.  Cardinality is unchanged, support is
transported to the normalized first vertex class, and the dot-difference set
lies in a `4 * sqrt rho` thickening of the normalized translated base slice.
-/
structure WZ1Lemma23NormalizedTripartitePackage
    (rho : ℝ) where
  sourceF : DiscreteSet 2
  sourceG₁ : DiscreteSet 2
  sourceG₂ : DiscreteSet 2
  sourceH : Finset (Point2 × Point2 × Point2)
  sourceValues : Finset ℝ
  F : DiscreteSet 2 :=
    wz1Lemma23NormalizedFirstVertices rho sourceF
  G₁ : DiscreteSet 2 := sourceG₁
  G₂ : DiscreteSet 2 := sourceG₂
  H : Finset (Point2 × Point2 × Point2) :=
    wz1Lemma23NormalizedEdges rho sourceH
  values : Finset ℝ :=
    wz1Lemma23NormalizedBaseValues rho sourceValues
  F_eq : F = wz1Lemma23NormalizedFirstVertices rho sourceF
  G₁_eq : G₁ = sourceG₁
  G₂_eq : G₂ = sourceG₂
  H_eq : H = wz1Lemma23NormalizedEdges rho sourceH
  values_eq : values = wz1Lemma23NormalizedBaseValues rho sourceValues
  edge_support :
    ∀ edge ∈ H,
      edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂
  card_eq : H.card = sourceH.card
  dot_containment :
    wz1DotDifferenceSet H ⊆
      Metric.cthickening (4 * Real.sqrt rho) (values : Set ℝ)

private lemma wz1Lemma23NormalizeEdge_injective
    {rho : ℝ} (hrho : 0 < rho) :
    Function.Injective (wz1Lemma23NormalizeEdge rho) := by
  intro first second h
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hfirst : first.1 = second.1 := by
    have hcoord :
        (1 / Real.sqrt rho) • first.1 =
          (1 / Real.sqrt rho) • second.1 :=
      congr_arg Prod.fst h
    exact
      smul_right_injective Point2
        (one_div_ne_zero hsqrt.ne') hcoord
  have hsecond1 : first.2.1 = second.2.1 :=
    congr_arg (fun edge => edge.2.1) h
  have hsecond2 : first.2.2 = second.2.2 :=
    congr_arg (fun edge => edge.2.2) h
  exact Prod.ext hfirst (Prod.ext hsecond1 hsecond2)

/-- Normalize one actual package at the paper's `sqrt rho` scale. -/
theorem WZ1Lemma23ActualTripartitePackage.normalize
    {rho : ℝ} (hrho : 0 < rho)
    {f g : ℝ → ℝ} {cells : Finset (ℤ × ℤ × ℤ)}
    {baseHeightIndex baseGlobalBin : ℤ}
    (package :
      WZ1Lemma23ActualTripartitePackage
        rho f g cells baseHeightIndex baseGlobalBin) :
    ∃ normalized : WZ1Lemma23NormalizedTripartitePackage rho,
      normalized.sourceF = package.F ∧
      normalized.sourceG₁ = package.G₁ ∧
      normalized.sourceG₂ = package.G₂ ∧
      normalized.sourceH = package.H ∧
      normalized.sourceValues =
        wz1Lemma23SnappedBaseSliceValues
          rho f cells baseHeightIndex baseGlobalBin := by
  let values :=
    wz1Lemma23SnappedBaseSliceValues
      rho f cells baseHeightIndex baseGlobalBin
  let normalizedH := wz1Lemma23NormalizedEdges rho package.H
  let normalizedF := wz1Lemma23NormalizedFirstVertices rho package.F
  let normalizedValues := wz1Lemma23NormalizedBaseValues rho values
  have hsupport :
      ∀ edge ∈ normalizedH,
        edge.1 ∈ normalizedF ∧
        edge.2.1 ∈ package.G₁ ∧
        edge.2.2 ∈ package.G₂ := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with
      ⟨sourceEdge, hsourceEdge, rfl⟩
    have hs := package.edge_support sourceEdge hsourceEdge
    exact
      ⟨Finset.mem_image.mpr ⟨sourceEdge.1, hs.1, rfl⟩,
        hs.2.1, hs.2.2⟩
  have hcard : normalizedH.card = package.H.card := by
    exact Finset.card_image_of_injective
      package.H
      (wz1Lemma23NormalizeEdge_injective hrho)
  have hdot :
      wz1DotDifferenceSet normalizedH ⊆
        Metric.cthickening (4 * Real.sqrt rho)
          (normalizedValues : Set ℝ) := by
    intro value hvalue
    change value ∈
      normalizedH.image
        (fun edge =>
          inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hvalue
    have hvalue' :
        value ∈
          normalizedH.image
            (fun edge =>
              inner ℝ edge.1 (edge.2.1 - edge.2.2)) :=
      Finset.mem_coe.mp hvalue
    rcases Finset.mem_image.mp hvalue' with
      ⟨normalizedEdge, hedge, rfl⟩
    rcases Finset.mem_image.mp hedge with
      ⟨sourceEdge, hsourceEdge, rfl⟩
    let sourceDot :=
      inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2)
    have hsourceDot :
        sourceDot ∈ wz1DotDifferenceSet package.H := by
      change sourceDot ∈
        package.H.image
          (fun edge =>
            inner ℝ edge.1 (edge.2.1 - edge.2.2))
      exact Finset.mem_image.mpr
        ⟨sourceEdge, hsourceEdge, rfl⟩
    have hnear :
        sourceDot ∈
          Metric.cthickening (4 * rho) (values : Set ℝ) := by
      simpa [values] using package.dot_containment hsourceDot
    have hcompact : IsCompact (values : Set ℝ) :=
      (values : Set ℝ).toFinite.isCompact
    rw [hcompact.cthickening_eq_biUnion_closedBall
      (by positivity)] at hnear
    rcases Set.mem_iUnion₂.mp hnear with
      ⟨sourceValue, hsourceValue, hdist⟩
    have hdist' : dist sourceDot sourceValue ≤ 4 * rho := by
      simpa [Metric.mem_closedBall] using hdist
    let targetValue := sourceValue / Real.sqrt rho
    have htargetValue : targetValue ∈ normalizedValues := by
      exact Finset.mem_image.mpr
        ⟨sourceValue, Finset.mem_coe.mp hsourceValue, rfl⟩
    refine Metric.mem_cthickening_of_dist_le
      (inner ℝ
        ((1 / Real.sqrt rho) • sourceEdge.1)
        (sourceEdge.2.1 - sourceEdge.2.2))
      targetValue
      (4 * Real.sqrt rho)
      (normalizedValues : Set ℝ)
      htargetValue ?_
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
    have hinner :
        inner ℝ ((1 / Real.sqrt rho) • sourceEdge.1)
            (sourceEdge.2.1 - sourceEdge.2.2) =
          sourceDot / Real.sqrt rho := by
      simp [sourceDot, inner_smul_left]
      ring
    rw [hinner]
    change dist (sourceDot / Real.sqrt rho)
        (sourceValue / Real.sqrt rho) ≤
      4 * Real.sqrt rho
    rw [Real.dist_eq]
    have habs : |sourceDot - sourceValue| ≤ 4 * rho := by
      simpa [Real.dist_eq] using hdist'
    have hscaled :
        |sourceDot / Real.sqrt rho -
            sourceValue / Real.sqrt rho| =
          |sourceDot - sourceValue| / Real.sqrt rho := by
      rw [← sub_div, abs_div, abs_of_pos hsqrt]
    rw [hscaled]
    calc
      |sourceDot - sourceValue| / Real.sqrt rho
          ≤ (4 * rho) / Real.sqrt rho := by gcongr
      _ = 4 * Real.sqrt rho := by
        apply (div_eq_iff hsqrt.ne').2
        nlinarith [Real.sq_sqrt hrho.le]
  let normalized :
      WZ1Lemma23NormalizedTripartitePackage rho :=
    { sourceF := package.F
      sourceG₁ := package.G₁
      sourceG₂ := package.G₂
      sourceH := package.H
      sourceValues := values
      F := normalizedF
      G₁ := package.G₁
      G₂ := package.G₂
      H := normalizedH
      values := normalizedValues
      F_eq := rfl
      G₁_eq := rfl
      G₂_eq := rfl
      H_eq := rfl
      values_eq := rfl
      edge_support := hsupport
      card_eq := hcard
      dot_containment := hdot }
  exact ⟨normalized, rfl, rfl, rfl, rfl, rfl⟩

end

end Kakeya.Assouad
