import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RotationTransfer
import MyLeanRepo.Kakeya.CV.PrincipalAxes.CoordinatePermutation
import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalAffinePatchMeasurable
import MyLeanRepo.Kakeya.CV.GeometricMeasure.DirectionalSurfaceAreaTransport
import MyLeanRepo.Kakeya.CV.Geometry
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaWeightedOnOpen
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Per-direction affine patch identity

Given the direction-2 patch identity, derive the direction-i version by
conjugating with `coordPerm i`.
-/

noncomputable section

open MeasureTheory Metric Set Finset
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

/-- Direction-i patch identity, derived from the direction-2 identity by
conjugating with the coordinate permutation `coordPerm i`. -/
lemma direction_i_patch_identity
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    (i : Fin 3)
    {U : Set R2} {g : R2 → ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (h_zero : ∀ u ∈ U, polynomialValue q (coordPerm i (graphMap g u)) = 0)
    (h_reg : ∀ u ∈ U,
      (polynomialGradient q (coordPerm i (graphMap g u))) i ≠ 0) :
    ENNReal.ofReal (ℓ i) *
      directionalSurfaceArea (b i) p
        ((fun y => z + η • A y) '' (coordPerm i '' (graphMap g '' U))) =
    ENNReal.ofReal
        (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
      directionalSurfaceArea (eBasis i) q
        (coordPerm i '' (graphMap g '' U)) := by
  let P : Point 3 ≃ₗᵢ[ℝ] Point 3 := coordPerm i
  let P' : Point 3 ≃ₗ[ℝ] Point 3 := P.toLinearEquiv
  let p' : MvPolynomial (Fin 3) ℝ := rotatedPoly p P
  let q' : MvPolynomial (Fin 3) ℝ := rotatedPoly q P
  let A' : Point 3 ≃ₗ[ℝ] Point 3 := P'.trans (A.trans P')
  let z' : Point 3 := P z
  let b' : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
    (b.map P).reindex (coordPermEquiv i)
  let ℓ' : Fin 3 → ℝ := fun j => ℓ ((coordPermEquiv i) j)
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let f' : Point 3 → Point 3 := fun y => z' + η • A' y
  let G : Set (Point 3) := graphMap g '' U

  have hb'_apply :
      ∀ j : Fin 3, b' j = P (b ((coordPermEquiv i) j)) := by
    intro j
    rw [OrthonormalBasis.reindex_apply]
    rfl

  have hA' : ∀ j : Fin 3, A' (eBasis j) = ℓ' j • b' j := by
    intro j
    have h1 : A' (eBasis j) = P (A (P (eBasis j))) := by
      rfl
    rw [h1]
    have h2 : P (eBasis j) = eBasis ((coordPermEquiv i) j) :=
      coordPerm_basis i j
    rw [h2]
    have h3 :
        A (eBasis ((coordPermEquiv i) j)) =
          ℓ ((coordPermEquiv i) j) • b ((coordPermEquiv i) j) :=
      hA ((coordPermEquiv i) j)
    rw [h3]
    have h4 :
        P (ℓ ((coordPermEquiv i) j) • b ((coordPermEquiv i) j)) =
          ℓ ((coordPermEquiv i) j) • P (b ((coordPermEquiv i) j)) := by
      rw [P.map_smul]
    rw [h4, hb'_apply]

  have hpq' :
      ∀ x, polynomialValue p' (z' + η • A' x) =
        polynomialValue q' x := by
    intro x
    have h1 : z' + η • A' x = P (z + η • A (P x)) := by
      have h2 : A' x = P (A (P x)) := by rfl
      simp [z', h2, P.map_add, P.map_smul]
    rw [h1]
    have h3 :
        polynomialValue p' (P (z + η • A (P x))) =
          polynomialValue p (z + η • A (P x)) :=
      rotatedPoly_eval p P (z + η • A (P x))
    rw [h3, hpq (P x)]
    have h4 :
        polynomialValue q' (P (P x)) =
          polynomialValue q (P x) :=
      rotatedPoly_eval q P (P x)
    have h5 : P (P x) = x := coordPerm_involutive i x
    rw [h5] at h4
    exact h4.symm

  have h_zero' :
      ∀ u ∈ U, polynomialValue q' (graphMap g u) = 0 := by
    intro u hu
    have h3 :
        polynomialValue q' (graphMap g u) =
          polynomialValue q (P (graphMap g u)) := by
      have h4 :
          P (P (graphMap g u)) = graphMap g u :=
        coordPerm_involutive i (graphMap g u)
      have h5 := rotatedPoly_eval q P (P (graphMap g u))
      rw [h4] at h5
      exact h5
    exact h3.trans (h_zero u hu)

  have h_reg' :
      ∀ u ∈ U, (polynomialGradient q' (graphMap g u)) 2 ≠ 0 := by
    intro u hu
    have h1 :
        (polynomialGradient q' (graphMap g u)) 2 =
          (polynomialGradient q (P (graphMap g u))) i := by
      have h2 := coordPerm_gradient_component q i (P (graphMap g u))
      have h3 :
          P (P (graphMap g u)) = graphMap g u :=
        coordPerm_involutive i (graphMap g u)
      rw [h3] at h2
      exact h2
    rw [h1]
    exact h_reg u hu

  have h_det :
      |LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3)| =
        |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := by
    have h1 :
        LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3) =
          LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) := by
      change LinearMap.det
          ((P' : Point 3 →ₗ[ℝ] Point 3).comp
            ((A : Point 3 →ₗ[ℝ] Point 3).comp
              (P' : Point 3 →ₗ[ℝ] Point 3))) =
        _
      rw [LinearMap.det_comp, LinearMap.det_comp]
      ring
    have hP_comp :
        (P' : Point 3 →ₗ[ℝ] Point 3).comp
            (P' : Point 3 →ₗ[ℝ] Point 3) =
          LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact coordPerm_involutive i x
    have h2 :
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) =
          1 := by
      calc
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3)
            = LinearMap.det
                ((P' : Point 3 →ₗ[ℝ] Point 3).comp
                  (P' : Point 3 →ₗ[ℝ] Point 3)) := by
                rw [LinearMap.det_comp]
        _ = LinearMap.det (LinearMap.id : Point 3 →ₗ[ℝ] Point 3) := by
              rw [hP_comp]
        _ = 1 := by simp
    rw [h1]
    have h3 :
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) =
            (LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3)) *
              LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) := by
      ring
    rw [h3, h2, one_mul]

  have h_patch2' := affine_patch_identity_dir2_meas
    (B := U)
    p' q' A' η z' hη b' ℓ'
    (fun j => hℓ ((coordPermEquiv i) j)) hA' hpq'
    hU hg hU.measurableSet subset_rfl h_zero' h_reg'

  have hℓ'2 : ℓ' 2 = ℓ i := by
    dsimp only [ℓ']
    have h : coordPermEquiv i 2 = i := by
      simp [coordPermEquiv]
    rw [h]

  have hP_image : P '' (f '' (P '' G)) = f' '' G := by
    have h1 : ∀ x, P (f (P x)) = f' x := by
      intro x
      have h2 : f (P x) = z + η • A (P x) := by rfl
      rw [h2]
      have h3 : P (z + η • A (P x)) = z' + η • A' x := by
        have hA' : A' x = P (A (P x)) := by rfl
        simp [z', hA', P.map_add, P.map_smul]
      exact h3
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hxG, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hxG, (h1 x).symm⟩
    · rintro ⟨x, hxG, rfl⟩
      exact ⟨f (P x), ⟨P x, ⟨x, hxG, rfl⟩, rfl⟩, h1 x⟩

  have hb'2 : b' 2 = P (b i) := by
    rw [hb'_apply]
    have h : coordPermEquiv i 2 = i := by
      simp [coordPermEquiv]
    rw [h]

  have h_transfer_lhs :
      directionalSurfaceArea (b' 2) p' (f' '' G) =
        directionalSurfaceArea (b i) p (f '' (P '' G)) := by
    have h :=
      directionalSurfaceArea_transfer_general p P (b i) (f '' (P '' G))
    rw [hb'2, show p' = rotatedPoly p P by rfl, ← hP_image]
    exact h

  have h_transfer_rhs :
      directionalSurfaceArea (eBasis 2) q' G =
        directionalSurfaceArea (eBasis i) q (P '' G) := by
    have h :=
      directionalSurfaceArea_transfer_general q P (eBasis i) (P '' G)
    have hPP : P '' (P '' G) = G := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        rw [coordPerm_involutive i x]
        exact hx
      · intro hy
        exact ⟨P y, ⟨y, hy, rfl⟩, coordPerm_involutive i y⟩
    rw [coordPerm_basis_j, hPP] at h
    exact h

  calc
    ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' (P '' G))
        = ENNReal.ofReal (ℓ' 2) *
          directionalSurfaceArea (b i) p (f '' (P '' G)) := by
            rw [hℓ'2]
    _ = ENNReal.ofReal (ℓ' 2) *
          directionalSurfaceArea (b' 2) p' (f' '' G) := by
            rw [h_transfer_lhs]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis 2) q' G := h_patch2'
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis 2) q' G := by
            rw [h_det]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis i) q (P '' G) := by
            rw [h_transfer_rhs]

/-- Direction-i measurable patch identity: same as `direction_i_patch_identity`
but the graph base `B` is a measurable subset of the open regularity set `U`. -/
lemma direction_i_patch_identity_meas
    (p q : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) (hη : 0 < η)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hpq : ∀ x, polynomialValue p (z + η • A x) = polynomialValue q x)
    (i : Fin 3)
    {U : Set R2} {g : R2 → ℝ} {B : Set R2}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hB : MeasurableSet B) (hB_sub : B ⊆ U)
    (h_zero : ∀ u ∈ U, polynomialValue q (coordPerm i (graphMap g u)) = 0)
    (h_reg : ∀ u ∈ U,
      (polynomialGradient q (coordPerm i (graphMap g u))) i ≠ 0) :
    ENNReal.ofReal (ℓ i) *
      directionalSurfaceArea (b i) p
        ((fun y => z + η • A y) '' (coordPerm i '' (graphMap g '' B))) =
    ENNReal.ofReal
        (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
      directionalSurfaceArea (eBasis i) q
        (coordPerm i '' (graphMap g '' B)) := by
  let P : Point 3 ≃ₗᵢ[ℝ] Point 3 := coordPerm i
  let P' : Point 3 ≃ₗ[ℝ] Point 3 := P.toLinearEquiv
  let p' : MvPolynomial (Fin 3) ℝ := rotatedPoly p P
  let q' : MvPolynomial (Fin 3) ℝ := rotatedPoly q P
  let A' : Point 3 ≃ₗ[ℝ] Point 3 := P'.trans (A.trans P')
  let z' : Point 3 := P z
  let b' : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
    (b.map P).reindex (coordPermEquiv i)
  let ℓ' : Fin 3 → ℝ := fun j => ℓ ((coordPermEquiv i) j)
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let f' : Point 3 → Point 3 := fun y => z' + η • A' y
  let G : Set (Point 3) := graphMap g '' B

  have hb'_apply :
      ∀ j : Fin 3, b' j = P (b ((coordPermEquiv i) j)) := by
    intro j
    rw [OrthonormalBasis.reindex_apply]
    rfl

  have hA' : ∀ j : Fin 3, A' (eBasis j) = ℓ' j • b' j := by
    intro j
    have h1 : A' (eBasis j) = P (A (P (eBasis j))) := by rfl
    rw [h1]
    have h2 : P (eBasis j) = eBasis ((coordPermEquiv i) j) :=
      coordPerm_basis i j
    rw [h2]
    have h3 :
        A (eBasis ((coordPermEquiv i) j)) =
          ℓ ((coordPermEquiv i) j) • b ((coordPermEquiv i) j) :=
      hA ((coordPermEquiv i) j)
    rw [h3]
    have h4 :
        P (ℓ ((coordPermEquiv i) j) • b ((coordPermEquiv i) j)) =
          ℓ ((coordPermEquiv i) j) • P (b ((coordPermEquiv i) j)) := by
      rw [P.map_smul]
    rw [h4, hb'_apply]

  have hpq' :
      ∀ x, polynomialValue p' (z' + η • A' x) =
        polynomialValue q' x := by
    intro x
    have h1 : z' + η • A' x = P (z + η • A (P x)) := by
      have h2 : A' x = P (A (P x)) := by rfl
      simp [z', h2, P.map_add, P.map_smul]
    rw [h1]
    have h3 :
        polynomialValue p' (P (z + η • A (P x))) =
          polynomialValue p (z + η • A (P x)) :=
      rotatedPoly_eval p P (z + η • A (P x))
    rw [h3, hpq (P x)]
    have h4 :
        polynomialValue q' (P (P x)) =
          polynomialValue q (P x) :=
      rotatedPoly_eval q P (P x)
    have h5 : P (P x) = x := coordPerm_involutive i x
    rw [h5] at h4
    exact h4.symm

  have h_zero' :
      ∀ u ∈ U, polynomialValue q' (graphMap g u) = 0 := by
    intro u hu
    have h3 :
        polynomialValue q' (graphMap g u) =
          polynomialValue q (P (graphMap g u)) := by
      have h4 :
          P (P (graphMap g u)) = graphMap g u :=
        coordPerm_involutive i (graphMap g u)
      have h5 := rotatedPoly_eval q P (P (graphMap g u))
      rw [h4] at h5
      exact h5
    exact h3.trans (h_zero u hu)

  have h_reg' :
      ∀ u ∈ U, (polynomialGradient q' (graphMap g u)) 2 ≠ 0 := by
    intro u hu
    have h1 :
        (polynomialGradient q' (graphMap g u)) 2 =
          (polynomialGradient q (P (graphMap g u))) i := by
      have h2 := coordPerm_gradient_component q i (P (graphMap g u))
      have h3 :
          P (P (graphMap g u)) = graphMap g u :=
        coordPerm_involutive i (graphMap g u)
      rw [h3] at h2
      exact h2
    rw [h1]
    exact h_reg u hu

  have h_det :
      |LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3)| =
        |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := by
    have h1 :
        LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3) =
          LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) := by
      change LinearMap.det
          ((P' : Point 3 →ₗ[ℝ] Point 3).comp
            ((A : Point 3 →ₗ[ℝ] Point 3).comp
              (P' : Point 3 →ₗ[ℝ] Point 3))) =
        _
      rw [LinearMap.det_comp, LinearMap.det_comp]
      ring
    have hP_comp :
        (P' : Point 3 →ₗ[ℝ] Point 3).comp
            (P' : Point 3 →ₗ[ℝ] Point 3) =
          LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact coordPerm_involutive i x
    have h2 :
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
            LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) =
          1 := by
      calc
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3)
            = LinearMap.det
                ((P' : Point 3 →ₗ[ℝ] Point 3).comp
                  (P' : Point 3 →ₗ[ℝ] Point 3)) := by
                rw [LinearMap.det_comp]
        _ = LinearMap.det (LinearMap.id : Point 3 →ₗ[ℝ] Point 3) := by
              rw [hP_comp]
        _ = 1 := by simp
    rw [h1]
    have h3 :
        LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) =
            (LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3) *
              LinearMap.det (P' : Point 3 →ₗ[ℝ] Point 3)) *
              LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) := by
      ring
    rw [h3, h2, one_mul]

  have h_patch2' := affine_patch_identity_dir2_meas
    p' q' A' η z' hη b' ℓ'
    (fun j => hℓ ((coordPermEquiv i) j)) hA' hpq'
    hU hg hB hB_sub h_zero' h_reg'

  have hℓ'2 : ℓ' 2 = ℓ i := by
    dsimp only [ℓ']
    have h : coordPermEquiv i 2 = i := by
      simp [coordPermEquiv]
    rw [h]

  have hP_image : P '' (f '' (P '' G)) = f' '' G := by
    have h1 : ∀ x, P (f (P x)) = f' x := by
      intro x
      have h2 : f (P x) = z + η • A (P x) := by rfl
      rw [h2]
      have h3 : P (z + η • A (P x)) = z' + η • A' x := by
        have hA' : A' x = P (A (P x)) := by rfl
        simp [z', hA', P.map_add, P.map_smul]
      exact h3
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hxG, rfl⟩, rfl⟩, rfl⟩
      exact ⟨x, hxG, (h1 x).symm⟩
    · rintro ⟨x, hxG, rfl⟩
      exact ⟨f (P x), ⟨P x, ⟨x, hxG, rfl⟩, rfl⟩, h1 x⟩

  have hb'2 : b' 2 = P (b i) := by
    rw [hb'_apply]
    have h : coordPermEquiv i 2 = i := by
      simp [coordPermEquiv]
    rw [h]

  have h_transfer_lhs :
      directionalSurfaceArea (b' 2) p' (f' '' G) =
        directionalSurfaceArea (b i) p (f '' (P '' G)) := by
    have h :=
      directionalSurfaceArea_transfer_general p P (b i) (f '' (P '' G))
    rw [hb'2, show p' = rotatedPoly p P by rfl, ← hP_image]
    exact h

  have h_transfer_rhs :
      directionalSurfaceArea (eBasis 2) q' G =
        directionalSurfaceArea (eBasis i) q (P '' G) := by
    have h :=
      directionalSurfaceArea_transfer_general q P (eBasis i) (P '' G)
    have hPP : P '' (P '' G) = G := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        rw [coordPerm_involutive i x]
        exact hx
      · intro hy
        exact ⟨P y, ⟨y, hy, rfl⟩, coordPerm_involutive i y⟩
    rw [coordPerm_basis_j, hPP] at h
    exact h

  calc
    ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' (P '' G))
        = ENNReal.ofReal (ℓ' 2) *
          directionalSurfaceArea (b i) p (f '' (P '' G)) := by
            rw [hℓ'2]
    _ = ENNReal.ofReal (ℓ' 2) *
          directionalSurfaceArea (b' 2) p' (f' '' G) := by
            rw [h_transfer_lhs]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A' : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis 2) q' G := h_patch2'
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis 2) q' G := by
            rw [h_det]
    _ = ENNReal.ofReal
          (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          directionalSurfaceArea (eBasis i) q (P '' G) := by
            rw [h_transfer_rhs]

end Kakeya.CV
