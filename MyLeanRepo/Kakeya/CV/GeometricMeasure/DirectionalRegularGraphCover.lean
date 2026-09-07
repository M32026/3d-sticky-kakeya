import MyLeanRepo.Kakeya.CV.PolynomialCylinder.ImplicitCover
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaMain
import MyLeanRepo.Kakeya.CV.PrincipalAxes.CoordinatePermutation

/-!
# Directional regular graph covers

For a fixed coordinate direction, transport the countable vertical graph
cover of a polynomial's regular zero set through the corresponding coordinate
permutation. Each returned patch retains both its zero-set property and
nonvanishing of the selected gradient component.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.CV

/-- A vertical graph set is the image of its base under `graphMap`. -/
lemma zGraph_eq_graphMap_image {U : Set (Point 2)} {f : Point 2 → ℝ} :
    zGraph U f = graphMap f '' U := by
  ext x
  simp only [zGraph, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨proj2 x, hx.1, ?_⟩
    exact graphMap_proj2_eq hx
  · rintro ⟨y, hy, rfl⟩
    have h_proj : proj2 (graphMap f y) = y := proj2_graphMap_eq f y
    constructor
    · rw [h_proj]
      exact hy
    · have h2 : (graphMap f y) 2 = f y := by
        simp [graphMap]
      rw [h2, h_proj]

/-- Countably cover the zero-set locus regular in coordinate `i` by
coordinate-permuted open graph patches. -/
lemma direction_i_graph_cover (q : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    ∃ (patches : ℕ → Set (Point 3))
      (U : ℕ → Set (Point 2))
      (g : ℕ → Point 2 → ℝ),
      (∀ n, IsOpen (U n) ∧ ContDiffOn ℝ 1 (g n) (U n) ∧
        patches n = coordPerm i '' (graphMap (g n) '' U n) ∧
        (∀ u ∈ U n,
          polynomialValue q (coordPerm i (graphMap (g n) u)) = 0) ∧
        (∀ u ∈ U n,
          (polynomialGradient q
            (coordPerm i (graphMap (g n) u))) i ≠ 0)) ∧
      {x : Point 3 |
        polynomialValue q x = 0 ∧
          (polynomialGradient q x) i ≠ 0} ⊆
        ⋃ n, patches n := by
  let q' : MvPolynomial (Fin 3) ℝ := rotatedPoly q (coordPerm i)
  let P : Point 3 ≃ₗᵢ[ℝ] Point 3 := coordPerm i
  obtain ⟨zpatches, hpatch_props, hcover⟩ :=
    regular_zero_set_zGraph_cover q'
  choose U g hU_open hg_diff h_eq h_zpatch_zero h_zpatch_reg using
    hpatch_props
  let patches : ℕ → Set (Point 3) := fun n => P '' zpatches n
  have h_zgraph_eq :
      ∀ n, zpatches n = graphMap (g n) '' U n := by
    intro n
    rw [h_eq n, zGraph_eq_graphMap_image]
  have h_zero :
      ∀ n u, u ∈ U n →
        polynomialValue q (P (graphMap (g n) u)) = 0 := by
    intro n u hu
    have h1 : graphMap (g n) u ∈ zpatches n := by
      rw [h_zgraph_eq n]
      exact ⟨u, hu, rfl⟩
    have h2 : graphMap (g n) u ∈ polynomialZeroSet q' :=
      h_zpatch_zero n h1
    let y := graphMap (g n) u
    have h3 : polynomialValue q' y = 0 := by
      simpa [polynomialZeroSet] using h2
    have h4 : polynomialValue q' y = polynomialValue q (P y) := by
      have h5 : P (P y) = y := coordPerm_involutive i y
      have h6 :
          polynomialValue q' (P (P y)) = polynomialValue q (P y) :=
        rotatedPoly_eval q P (P y)
      rw [h5] at h6
      exact h6
    rw [h4] at h3
    exact h3
  have h_reg :
      ∀ n u, u ∈ U n →
        (polynomialGradient q (P (graphMap (g n) u))) i ≠ 0 := by
    intro n u hu
    have h1 : graphMap (g n) u ∈ zpatches n := by
      rw [h_zgraph_eq n]
      exact ⟨u, hu, rfl⟩
    have h2 :
        (polynomialGradient q' (graphMap (g n) u)) 2 ≠ 0 :=
      h_zpatch_reg n (graphMap (g n) u) h1
    have h3 :
        (polynomialGradient q' (graphMap (g n) u)) 2 =
          (polynomialGradient q (P (graphMap (g n) u))) i := by
      have h4 := coordPerm_gradient_component q i
        (P (graphMap (g n) u))
      have h5 :
          P (P (graphMap (g n) u)) = graphMap (g n) u :=
        coordPerm_involutive i _
      rw [h5] at h4
      exact h4
    rw [h3] at h2
    exact h2
  refine ⟨patches, U, g, ?_, ?_⟩
  · intro n
    exact ⟨hU_open n, hg_diff n, by
      rw [show patches n = P '' zpatches n by rfl, h_zgraph_eq n],
      h_zero n, h_reg n⟩
  · intro x hx
    let y := P x
    have hy1 : polynomialValue q' y = 0 := by
      exact (coordPerm_zeroSet_transfer q i x).trans hx.1
    have hy2 : (polynomialGradient q' y) 2 ≠ 0 := by
      rw [show y = coordPerm i x by rfl,
        coordPerm_gradient_component q i x]
      exact hx.2
    have hy_in :
        y ∈ {z ∈ polynomialZeroSet q' |
          (polynomialGradient q' z) 2 ≠ 0} :=
      ⟨hy1, hy2⟩
    have h3 : y ∈ ⋃ n, zpatches n := hcover hy_in
    rcases Set.mem_iUnion.mp h3 with ⟨n, hn⟩
    have h4 : x ∈ patches n := by
      change x ∈ P '' zpatches n
      exact ⟨y, hn, coordPerm_involutive i x⟩
    exact Set.mem_iUnion.mpr ⟨n, h4⟩

end Kakeya.CV
