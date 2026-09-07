import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer

/-!
# Coordinate permutations for principal-axis directional covers

The map `coordPerm j` swaps coordinates `j` and `2`. The accompanying lemmas
transfer regular graph directions and show that the sum of coordinate
directional surface areas is invariant under the permutation.
-/

noncomputable section

open Set MeasureTheory Metric Finset
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

/-- Coordinate permutation swapping indices `j` and `2` on `Fin 3`. -/
def coordPermEquiv (j : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap j 2

/-- Linear isometry equivalence on `Point 3` swapping coordinates `j` and `2`. -/
def coordPerm (j : Fin 3) : Point 3 ≃ₗᵢ[ℝ] Point 3 :=
  LinearIsometryEquiv.piLpCongrLeft (2 : ENNReal) ℝ ℝ (coordPermEquiv j)

lemma coordPerm_apply (j : Fin 3) (x : Point 3) (k : Fin 3) :
    (coordPerm j x) k = x ((coordPermEquiv j) k) := by
  simp [coordPerm, LinearIsometryEquiv.piLpCongrLeft_apply]
  <;> rfl

lemma coordPermEquiv_involutive (j : Fin 3) :
    (coordPermEquiv j).symm = coordPermEquiv j := by
  ext k
  simp [coordPermEquiv]
  <;> aesop

lemma coordPerm_symm (j : Fin 3) : (coordPerm j).symm = coordPerm j := by
  have h := coordPermEquiv_involutive j
  ext x
  simp [coordPerm, LinearIsometryEquiv.piLpCongrLeft_symm, h]
  <;> rfl

lemma coordPermEquiv_self_apply (j : Fin 3) (k : Fin 3) :
    coordPermEquiv j (coordPermEquiv j k) = k := by
  have h : (coordPermEquiv j).symm = coordPermEquiv j :=
    coordPermEquiv_involutive j
  have h2 : (coordPermEquiv j).symm (coordPermEquiv j k) = k :=
    (coordPermEquiv j).left_inv k
  simpa [h] using h2

lemma coordPerm_involutive (j : Fin 3) (x : Point 3) :
    coordPerm j (coordPerm j x) = x := by
  ext k
  rw [coordPerm_apply, coordPerm_apply]
  rw [coordPermEquiv_self_apply]

lemma coordPerm_basis (j i : Fin 3) :
    coordPerm j (eBasis i) = eBasis (coordPermEquiv j i) := by
  ext k
  rw [coordPerm_apply]
  have h_iff : coordPermEquiv j k = i ↔ k = coordPermEquiv j i := by
    constructor
    · intro h
      have h5 :
          coordPermEquiv j (coordPermEquiv j k) = coordPermEquiv j i := by
        rw [h]
      rw [coordPermEquiv_self_apply] at h5
      exact h5
    · intro h
      rw [h]
      exact coordPermEquiv_self_apply j i
  simp [eBasis, EuclideanSpace.single, h_iff]
  <;> aesop

lemma coordPerm_basis_j (j : Fin 3) :
    coordPerm j (eBasis j) = eBasis 2 := by
  rw [coordPerm_basis]
  have h : coordPermEquiv j j = 2 := by
    simp [coordPermEquiv, Equiv.swap_apply_def]
  rw [h]

lemma coordPerm_basis_2 (j : Fin 3) :
    coordPerm j (eBasis 2) = eBasis j := by
  rw [coordPerm_basis]
  have h : coordPermEquiv j 2 = j := by
    simp [coordPermEquiv, Equiv.swap_apply_def]
  rw [h]

/-- Under `coordPerm j`, the `j`-th gradient component of `q` becomes the
`2`-nd component of `rotatedPoly q (coordPerm j)`. -/
lemma coordPerm_gradient_component
    (q : MvPolynomial (Fin 3) ℝ) (j : Fin 3) (x : Point 3) :
    (polynomialGradient (rotatedPoly q (coordPerm j)) (coordPerm j x)) 2 =
      (polynomialGradient q x) j := by
  have h1 :
      polynomialGradient (rotatedPoly q (coordPerm j)) (coordPerm j x) =
        coordPerm j (polynomialGradient q x) :=
    rotatedPoly_gradient q (coordPerm j) x
  rw [h1, coordPerm_apply]
  have h3 : coordPermEquiv j 2 = j := by
    simp [coordPermEquiv, Equiv.swap_apply_def]
  rw [h3]

/-- Nonvanishing of a selected gradient component transfers to the last
coordinate under `coordPerm`. -/
lemma coordPerm_regular_transfer
    (q : MvPolynomial (Fin 3) ℝ) (j : Fin 3) (x : Point 3)
    (h : (polynomialGradient q x) j ≠ 0) :
    (polynomialGradient (rotatedPoly q (coordPerm j)) (coordPerm j x)) 2 ≠ 0 := by
  rw [coordPerm_gradient_component q j x]
  exact h

/-- Polynomial values are preserved under the matching coordinate
permutation. -/
lemma coordPerm_zeroSet_transfer
    (q : MvPolynomial (Fin 3) ℝ) (j : Fin 3) (x : Point 3) :
    polynomialValue (rotatedPoly q (coordPerm j)) (coordPerm j x) =
      polynomialValue q x :=
  rotatedPoly_eval q (coordPerm j) x

/-- The `j`-regular zero set maps to the last-coordinate regular zero set
under `coordPerm j`. -/
lemma coordPerm_image_regular
    (q : MvPolynomial (Fin 3) ℝ) (j : Fin 3) :
    coordPerm j '' {
        x | polynomialValue q x = 0 ∧ (polynomialGradient q x) j ≠ 0} =
      {y |
        polynomialValue (rotatedPoly q (coordPerm j)) y = 0 ∧
          (polynomialGradient (rotatedPoly q (coordPerm j)) y) 2 ≠ 0} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨coordPerm_zeroSet_transfer q j x ▸ hx.1,
      coordPerm_regular_transfer q j x hx.2⟩
  · intro hy
    let x := coordPerm j y
    have hxy : coordPerm j x = y := coordPerm_involutive j y
    refine ⟨x, ?_, hxy⟩
    have h4 : polynomialValue q x = 0 := by
      have h5 := coordPerm_zeroSet_transfer q j x
      rw [hxy] at h5
      exact h5.symm.trans hy.1
    have h6 : (polynomialGradient q x) j ≠ 0 := by
      have h7 := coordPerm_gradient_component q j x
      rw [hxy] at h7
      exact h7 ▸ hy.2
    exact ⟨h4, h6⟩

/-- A permutation of the coordinate basis leaves the sum of coordinate
directional surface areas unchanged. -/
lemma directionalSurfaceArea_sum_perm_inv
    (q : MvPolynomial (Fin 3) ℝ) (S : Set (Point 3))
    (R : Point 3 ≃ₗᵢ[ℝ] Point 3)
    (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ i : Fin 3, R.symm (eBasis i) = eBasis (σ i)) :
    ∑ i : Fin 3, directionalSurfaceArea (R.symm (eBasis i)) q S =
      ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q S := by
  have h :
      ∑ i : Fin 3, directionalSurfaceArea (R.symm (eBasis i)) q S =
        ∑ i : Fin 3, directionalSurfaceArea (eBasis (σ i)) q S := by
    apply Finset.sum_congr rfl
    intro i _
    exact congr_arg
      (fun e : Point 3 => directionalSurfaceArea e q S) (hσ i)
  rw [h]
  have h2 :
      ∑ i : Fin 3, directionalSurfaceArea (eBasis (σ i)) q S =
        ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q S := by
    have h_inj : Set.InjOn σ (Finset.univ : Finset (Fin 3)) := by
      intro i _ j _ hij
      exact σ.injective hij
    have h3 :
        ∑ i : Fin 3, directionalSurfaceArea (eBasis (σ i)) q S =
          ∑ j ∈ Finset.image σ (Finset.univ : Finset (Fin 3)),
            directionalSurfaceArea (eBasis j) q S := by
      rw [Finset.sum_image h_inj]
      <;> rfl
    rw [h3]
    have h4 :
        Finset.image σ (Finset.univ : Finset (Fin 3)) =
          (Finset.univ : Finset (Fin 3)) := by
      simp
    rw [h4]
  exact h2

/-- The isometry `coordPerm j` permutes the coordinate basis. -/
lemma coordPerm_permutes_basis (j : Fin 3) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3,
      (coordPerm j).symm (eBasis i) = eBasis (σ i) := by
  use coordPermEquiv j
  intro i
  rw [coordPerm_symm]
  exact coordPerm_basis j i

/-- Sum invariance specialized to `coordPerm j`. -/
lemma directionalSurfaceArea_sum_coordPerm_inv
    (q : MvPolynomial (Fin 3) ℝ) (S : Set (Point 3)) (j : Fin 3) :
    ∑ i : Fin 3,
        directionalSurfaceArea ((coordPerm j).symm (eBasis i)) q S =
      ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q S := by
  rcases coordPerm_permutes_basis j with ⟨σ, hσ⟩
  exact directionalSurfaceArea_sum_perm_inv q S (coordPerm j) σ hσ

end Kakeya.CV
