import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.PrincipalAxes.SingleEllipsoidWeightedLowerBound
import MyLeanRepo.Kakeya.CV.GeometricMeasure.DirectionalSurfaceAreaAdditivity

/-!
# Principal-axis weighted many-bisections bound

Formalizes the affine-invariant weighted surface estimate used in CV Lemma 9,
including the 40/40 approximate-bisection form required after mollification.

Combines the single-ellipsoid bound with finite additivity of directional
surface area over pairwise-disjoint zero-set pieces.
-/

noncomputable section

open MeasureTheory Metric Set Finset
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

theorem principalAxes_many_bisections
    (hIsoperimetric : PolynomialRegionIsoperimetricStatement) :
    PrincipalAxesManyBisectionsStatement := by
  let r : ENNReal := ENNReal.ofReal cutsBallConstant
  have hr_pos : 0 < cutsBallConstant := cutsBallConstant_pos
  have hr0 : r ≠ 0 := by
    have h : 0 < r := ENNReal.ofReal_pos.mpr hr_pos
    exact h.ne'
  have hr1 : r ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  let C : NNReal := ⟨cutsBallConstant⁻¹, inv_nonneg.mpr hr_pos.le⟩
  have hC_pos : 0 < C := by
    have h : 0 < cutsBallConstant⁻¹ := inv_pos.mpr hr_pos
    exact NNReal.coe_pos.mp h
  have hC_coe : (C : ENNReal) = r⁻¹ := by
    have h5 : (C : ENNReal) = ENNReal.ofReal (C : ℝ) := by simp
    have h6 : (C : ℝ) = cutsBallConstant⁻¹ := by rfl
    rw [h5, h6]
    have h7 : ENNReal.ofReal cutsBallConstant⁻¹ = (ENNReal.ofReal cutsBallConstant)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hr_pos]
    exact h7
  refine' ⟨C, hC_pos, _⟩
  intro ι _ p A η z b ℓ hp hsing hη hη_le hℓ hA_basis hdisj hCut
  have hA : ∀ i, A (eBasis i) = ℓ i • b i := by
    intro i
    have h_eq : eBasis i = EuclideanSpace.basisFun (Fin 3) ℝ i := by
      ext j
      simp [eBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.single]
    rw [h_eq]
    exact hA_basis i
  let X : ENNReal := ENNReal.ofReal (η ^ 2 * ∏ i : Fin 3, ℓ i) *
      codimensionOneMeasure 3 (unitSphere 3)
  let a : Fin 3 → ENNReal := fun i => ENNReal.ofReal (ℓ i)
  let S : ι → Set (Point 3) := fun j =>
    polynomialZeroSet p ∩ scaledEllipsoid A η (z j)
  have h_single : ∀ j : ι,
      r * X ≤ ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j) := by
    intro j
    have h := single_ellipsoid_weighted_lower_bound
      hIsoperimetric p A η (z j) b ℓ hp hsing hη hℓ hA (hCut j)
    have h' : r * X ≤ ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j) := by
      have h_eq : r * X = (r * ENNReal.ofReal (η ^ 2 * ∏ i : Fin 3, ℓ i)) * codimensionOneMeasure 3 (unitSphere 3) := by
        simp [r, X]
        ring
      rw [h_eq]
      exact h
    exact h'
  have h_sum1 :
      (Fintype.card ι : ENNReal) * (r * X) ≤
      ∑ j : ι, ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j) := by
    calc
      (Fintype.card ι : ENNReal) * (r * X)
        = ∑ j : ι, (r * X) := by
          rw [Finset.sum_const, card_univ]
          ring
      _ ≤ ∑ j : ι, ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j) := by
          apply Finset.sum_le_sum
          intro j _
          exact h_single j
  have hS_meas : ∀ j : ι, MeasurableSet (S j) := by
    intro j
    have h1 : MeasurableSet (polynomialZeroSet p) := by
      have h_cont : Continuous (fun x : Point 3 => polynomialValue p x) := by
        have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
          (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.continuous_of_finiteDimensional
        have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f p) :=
          MvPolynomial.continuous_eval p
        exact h2.comp h1
      exact (isClosed_eq h_cont continuous_const).measurableSet
    have h2 : MeasurableSet (scaledEllipsoid A η (z j)) := by
      have h_compact : IsCompact (scaledEllipsoid A η (z j)) := by
        have h1 : IsCompact (Metric.closedBall (0 : Point 3) η) :=
          isCompact_closedBall 0 η
        have h2 : IsCompact (A '' Metric.closedBall (0 : Point 3) η) :=
          h1.image A.toContinuousLinearEquiv.continuous
        simpa [scaledEllipsoid] using h2.vadd (z j)
      exact h_compact.measurableSet
    exact h1.inter h2
  have hS_disj : Pairwise (fun j k : ι => Disjoint (S j) (S k)) := by
    intro j k hne
    have h : Disjoint (scaledEllipsoid A η (z j)) (scaledEllipsoid A η (z k)) :=
      hdisj hne
    have h1 : S j ⊆ scaledEllipsoid A η (z j) := fun x hx => hx.2
    have h2 : S k ⊆ scaledEllipsoid A η (z k) := fun x hx => hx.2
    exact h.mono h1 h2
  have h_add : ∀ i : Fin 3,
      ∑ j : ι, directionalSurfaceArea (b i) p (S j) =
      directionalSurfaceArea (b i) p (⋃ j : ι, S j) := by
    intro i
    exact (directionalSurfaceArea_finite_iUnion (b i) p S hS_disj hS_meas).symm
  have h_iUnion : (⋃ j : ι, S j) =
      polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j) := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨j, h1, h2⟩
      exact ⟨h1, ⟨j, h2⟩⟩
    · rintro ⟨h1, j, h2⟩
      exact ⟨j, h1, h2⟩
  have h_sum2 :
      ∑ j : ι, ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j) =
      ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p
        (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) := by
    calc
      ∑ j : ι, ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (S j)
        = ∑ i : Fin 3, ∑ j : ι, a i * directionalSurfaceArea (b i) p (S j) := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, a i * ∑ j : ι, directionalSurfaceArea (b i) p (S j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
      _ = ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p (⋃ j : ι, S j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_add i]
      _ = ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p
            (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h_iUnion]
  have h_main : r * ((Fintype.card ι : ENNReal) * X) ≤
      ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p
        (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) := by
    have h3 : r * ((Fintype.card ι : ENNReal) * X) =
        (Fintype.card ι : ENNReal) * (r * X) := by ring
    rw [h3]
    rw [h_sum2] at h_sum1
    exact h_sum1
  have h_final : (Fintype.card ι : ENNReal) * X ≤
      (C : ENNReal) * ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p
        (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) := by
    have h4 : (Fintype.card ι : ENNReal) * X ≤ r⁻¹ * ∑ i : Fin 3, a i * directionalSurfaceArea (b i) p
          (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) :=
      (ENNReal.mul_le_iff_le_inv hr0 hr1).mp h_main
    have hC : (C : ENNReal) = r⁻¹ := hC_coe
    rw [hC]
    exact h4
  have h_goal : (Fintype.card ι : ENNReal) * ENNReal.ofReal (η ^ 2 * ∏ i : Fin 3, ℓ i) *
      codimensionOneMeasure 3 (unitSphere 3) ≤
      (C : ENNReal) * ∑ i : Fin 3, ENNReal.ofReal (ℓ i) *
        directionalSurfaceArea (b i) p
          (polynomialZeroSet p ∩ ⋃ j : ι, scaledEllipsoid A η (z j)) := by
    have h_eq1 : (Fintype.card ι : ENNReal) * ENNReal.ofReal (η ^ 2 * ∏ i : Fin 3, ℓ i) *
        codimensionOneMeasure 3 (unitSphere 3) =
        (Fintype.card ι : ENNReal) * X := by
      simp [X]
      ring
    rw [h_eq1]
    exact h_final
  exact h_goal

end Kakeya.CV
