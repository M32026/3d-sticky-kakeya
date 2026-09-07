import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Helper lemmas for the Lemma 8.13 core assembly

Elementary consequences of standard separation, uniform triple support, and
small-scale negative powers.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
From `WZ1StandardSeparation`, any two points in `G₁` are at distance at most
`1 / 10`.
-/
lemma wz1_standard_separation_diameter
    {F G₁ G₂ : DiscreteSet 2}
    (hstd : WZ1StandardSeparation F G₁ G₂) :
    ∀ first ∈ G₁, ∀ second ∈ G₁, dist first second ≤ 1 / 10 :=
  hstd.2.1

/--
Every edge of a uniformly dense tripartite graph lies in its corresponding
vertex classes.
-/
lemma wz1_uniform_density_support
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {c : ENNReal}
    (hdensity : WZ1UniformTripleDensity c F G₁ G₂ H) :
    ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
  have h := hdensity.2.1
  intro edge hedge
  let enc := wz1TripleCoordinate edge
  have h0 := h enc (by
    simp only [enc, wz1EncodeTriples, Finset.mem_image]
    exact ⟨edge, hedge, rfl⟩) 0
  have h1 := h enc (by
    simp only [enc, wz1EncodeTriples, Finset.mem_image]
    exact ⟨edge, hedge, rfl⟩) 1
  have h2 := h enc (by
    simp only [enc, wz1EncodeTriples, Finset.mem_image]
    exact ⟨edge, hedge, rfl⟩) 2
  exact ⟨h0, h1, h2⟩

/-- For `0 < delta ≤ 1` and `eta > 0`, `delta ^ (-eta) ≥ 1`. -/
lemma wz1_delta_neg_eta_ge_one
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) :
    (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-eta) := by
  have h1 : (1 : ℝ) ≤ Real.rpow delta (-eta) := by
    have h2 : -eta ≤ 0 := by linarith
    have h3 : Real.rpow delta (-eta) ≥ Real.rpow delta 0 :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h2
    simpa using h3
  have h4 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow delta (-eta)) := by
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h1
  have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
  rw [h5]
  simpa [Kakeya.realRpowENN] using h4

/-- Real-valued version of `wz1_delta_neg_eta_ge_one`. -/
lemma wz1_delta_neg_eta_ge_one_real
    {delta eta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) :
    (1 : ℝ) ≤ Real.rpow delta (-eta) := by
  have h2 : -eta ≤ 0 := by linarith
  have h3 : Real.rpow delta (-eta) ≥ Real.rpow delta 0 :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h2
  simpa using h3

end Kakeya.Assouad
