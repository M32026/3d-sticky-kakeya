import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Small supporting lemmas for faithful Kaufman input

1. Uniform density weakening (monotonicity in c)
2. commonConstant lower bound from coarsening retention
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Uniform triple density is monotone in the density constant. -/
lemma wz1UniformTripleDensity_weaken
    {c₁ c₂ : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (h : WZ1UniformTripleDensity c₁ F G₁ G₂ H)
    (hc : c₂ ≤ c₁) :
    WZ1UniformTripleDensity c₂ F G₁ G₂ H := by
  have h1 : H.Nonempty := h.1
  have h2 : WZ1UniformHypergraphDensity c₁
      (wz1TripleVertexClasses F G₁ G₂)
      (wz1EncodeTriples H) := h.2
  refine ⟨h1, ?_⟩
  have h3 : ∀ edge ∈ wz1EncodeTriples H, ∀ i : Fin 3,
      edge i ∈ wz1TripleVertexClasses F G₁ G₂ i := h2.1
  have h4 : ∀ edge ∈ wz1EncodeTriples H,
      ∀ I : Finset (Fin 3),
        c₂ * wz1VertexCardProduct
            (wz1TripleVertexClasses F G₁ G₂)
            (Finset.univ \ I) ≤
          ((wz1HypergraphFiber (wz1EncodeTriples H) I edge).card : ENNReal) := by
    intro edge hedge I
    have h5 : c₁ * wz1VertexCardProduct
              (wz1TripleVertexClasses F G₁ G₂)
              (Finset.univ \ I) ≤
            ((wz1HypergraphFiber (wz1EncodeTriples H) I edge).card : ENNReal) :=
      h2.2 edge hedge I
    have h6 : c₂ * wz1VertexCardProduct
              (wz1TripleVertexClasses F G₁ G₂)
              (Finset.univ \ I) ≤
            c₁ * wz1VertexCardProduct
              (wz1TripleVertexClasses F G₁ G₂)
              (Finset.univ \ I) := by
      gcongr
    exact h6.trans h5
  exact ⟨h3, h4⟩

/-- The coarsening logarithmic loss is at least one when the source set is
nonempty. -/
lemma wz1Coarsening_logarithmicLoss_ge_one
    {E : DiscreteSet 2} {fineScale coarseScale : ℝ} {C : ENNReal}
    (coarsening : WZ1FrostmanCoarseningData E fineScale coarseScale 1 C)
    (hE_nonempty : E.Nonempty) :
    1 ≤ coarsening.logarithmicLoss := by
  have hE_pos : (0 : ENNReal) < E.enncard := by
    simpa [DiscreteSet.enncard, Finset.card_pos] using hE_nonempty
  have hE_ne_zero : E.enncard ≠ 0 := hE_pos.ne'
  have hE_ne_top : E.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have hretention : E.enncard ≤
      ENNReal.ofReal coarsening.logarithmicLoss *
        coarsening.selected.enncard :=
    coarsening.retention
  have hselected_subset : coarsening.selected.enncard ≤ E.enncard := by
    have h : coarsening.selected ⊆ E := coarsening.selected_subset
    have hcard : coarsening.selected.card ≤ E.card := Finset.card_le_card h
    simpa [DiscreteSet.enncard] using (Nat.cast_le.mpr hcard : (coarsening.selected.card : ENNReal) ≤ (E.card : ENNReal))
  have h : E.enncard ≤
      ENNReal.ofReal coarsening.logarithmicLoss * E.enncard := by
    calc
      E.enncard ≤ ENNReal.ofReal coarsening.logarithmicLoss *
            coarsening.selected.enncard := hretention
      _ ≤ ENNReal.ofReal coarsening.logarithmicLoss * E.enncard := by
        gcongr
  have hdiv : E.enncard / E.enncard ≤
      (ENNReal.ofReal coarsening.logarithmicLoss * E.enncard) / E.enncard :=
    ENNReal.div_le_div_right h E.enncard
  have hcancel : (ENNReal.ofReal coarsening.logarithmicLoss * E.enncard) / E.enncard =
      ENNReal.ofReal coarsening.logarithmicLoss :=
    ENNReal.mul_div_cancel_right hE_ne_zero hE_ne_top
  have hone : E.enncard / E.enncard = 1 := by
    rw [ENNReal.div_self hE_ne_zero hE_ne_top]
  rw [hone, hcancel] at hdiv
  have h' : (1 : ENNReal) ≤ ENNReal.ofReal coarsening.logarithmicLoss := hdiv
  have hlog_nonneg : 0 ≤ coarsening.logarithmicLoss :=
    coarsening.logarithmicLoss_pos.le
  have h'' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal coarsening.logarithmicLoss := by
    simpa using h'
  exact (ENNReal.ofReal_le_ofReal_iff hlog_nonneg).mp h''

/-- The representative constant is at least one. -/
lemma wz1Representative_constant_ge_one
    {E : DiscreteSet 2} {fineScale coarseScale sourceConstant : ℝ} {C : ENNReal}
    (coarsening : WZ1FrostmanCoarseningData E fineScale coarseScale 1 C)
    (hE_nonempty : E.Nonempty)
    (hsourceConstant : 1 ≤ sourceConstant) :
    1 ≤ 16200 * coarsening.logarithmicLoss * sourceConstant := by
  have hlog : 1 ≤ coarsening.logarithmicLoss :=
    wz1Coarsening_logarithmicLoss_ge_one coarsening hE_nonempty
  have hpos : 0 < coarsening.logarithmicLoss :=
    coarsening.logarithmicLoss_pos
  have h : 1 ≤ 16200 * coarsening.logarithmicLoss := by
    calc
      1 ≤ coarsening.logarithmicLoss := hlog
      _ = 1 * coarsening.logarithmicLoss := by ring
      _ ≤ 16200 * coarsening.logarithmicLoss := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hpos.le
  calc
    1 ≤ 16200 * coarsening.logarithmicLoss := h
    _ = 16200 * coarsening.logarithmicLoss * 1 := by ring
    _ ≤ 16200 * coarsening.logarithmicLoss * sourceConstant := by
      exact mul_le_mul_of_nonneg_left hsourceConstant
        (mul_nonneg (by norm_num) hpos.le)

end Kakeya.Assouad
