import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityTruncation

/-!
# Exact-multiplicity truncation as a paper refinement

The cellwise truncation loses at most a factor of two in mass.  Consequently
it is a `WZ1PaperRefinement` whenever the requested polylogarithmic fraction
is at most one half.  The construction uses the identity tube subfamily, so
the refined shading is definitionally the exact-multiplicity truncation.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The identity subfamily, used to regard a same-family truncation as a
genuine `WZ1PaperRefinement`. -/
private def node05IdentitySubfamily
    {delta : ℝ} (fine : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeSubfamily fine where
  family := fine
  embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
  tube_eq _ := rfl

/-- A factor-two exact-multiplicity truncation is a paper refinement for any
exponent whose refinement fraction absorbs that factor two. -/
noncomputable def PureWZ2Node05ExactMultiplicityTruncationData.toPaperRefinement
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (logExponent : ℕ)
    (hscalar :
      2 * wz1PaperRefinementFraction delta logExponent ≤ 1) :
    WZ1PaperRefinement Y logExponent where
  selected := node05IdentitySubfamily fine
  refined := truncation.truncated
  subshading := truncation.subshading
  retained_mass := by
    calc
      wz1PaperRefinementFraction delta logExponent * Y.mass ≤
          wz1PaperRefinementFraction delta logExponent *
            (2 * truncation.truncated.mass) :=
        mul_le_mul_right truncation.mass_retention _
      _ = (2 * wz1PaperRefinementFraction delta logExponent) *
            truncation.truncated.mass := by
        ac_rfl
      _ ≤ 1 * truncation.truncated.mass :=
        mul_le_mul_left hscalar _
      _ = truncation.truncated.mass := one_mul _

/-- The paper refinement produced from exact truncation retains the exact
multiplicity band, in the form used by the Node 5 interface. -/
theorem PureWZ2Node05ExactMultiplicityTruncationData.toPaperRefinement_multiplicityBand
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (logExponent : ℕ)
    (hscalar :
      2 * wz1PaperRefinementFraction delta logExponent ≤ 1) :
    Kakeya.Streamlined.Shading.HasConstantMultiplicity
      (truncation.toPaperRefinement logExponent hscalar).refined m (2 * m) := by
  intro point hpoint
  have h := truncation.exact_multiplicity point hpoint
  exact ⟨h.1, h.2.trans (by omega)⟩

/-- The exponent-one specialization requested by the scheduled Node 5
wiring. -/
noncomputable def PureWZ2Node05ExactMultiplicityTruncationData.toPaperRefinementOne
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (hscalar : 2 * wz1PaperRefinementFraction delta 1 ≤ 1) :
    WZ1PaperRefinement Y 1 :=
  truncation.toPaperRefinement 1 hscalar

/-- The exponent-one refinement has multiplicity between `m` and `2*m` at
every point of its union. -/
theorem PureWZ2Node05ExactMultiplicityTruncationData.toPaperRefinementOne_multiplicityBand
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta}
    {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (hscalar : 2 * wz1PaperRefinementFraction delta 1 ≤ 1) :
    Kakeya.Streamlined.Shading.HasConstantMultiplicity
      (truncation.toPaperRefinementOne hscalar).refined m (2 * m) :=
  truncation.toPaperRefinement_multiplicityBand 1 hscalar

end Kakeya.Assouad
