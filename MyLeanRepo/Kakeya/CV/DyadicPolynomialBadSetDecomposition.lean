import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Dyadic and coloured decomposition of polynomial bad sets

Builds the `S^(r),Θ(Q)` layer structure used in the polynomial visibility
argument.

## Proof route

1. Establish evenness of `coefficientSurfaceFunctional` under coefficient
   negation, via polynomial negation invariance of gradient, unit normal,
   and directional surface area.
2. Show `ballAverage` preserves evenness of the center using negation as a
   measure-preserving measurable embedding.
3. Deduce `concreteMollifiedVisibilityBody` is antipodally even.
4. Prove every `0 < v ≤ M` lies in a dyadic layer `2^(-r-1)*M < v ≤ 2^(-r)*M`
   using `Nat.floor` of `-log(v/M)/log 2`.
5. Decompose the positive-visibility bad set as a union of dyadic layers
   intersected with colour classes from the stable ellipsoid colouring.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal Real

namespace Kakeya.CV

/-- Evaluating the negation of a polynomial gives the negation of the value. -/
lemma polynomialValue_neg' (p : MvPolynomial (Fin 3) ℝ) (y : Point 3) :
    polynomialValue (-p) y = -polynomialValue p y := by
  simp [polynomialValue]

/-- The directional surface area is invariant under polynomial negation. -/
lemma directionalSurfaceArea_neg_polynomial
    (e : Point 3) (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)) :
    directionalSurfaceArea e (-p) s = directionalSurfaceArea e p s := by
  have h_pderiv : ∀ i : Fin 3,
      MvPolynomial.pderiv i (-p) = -MvPolynomial.pderiv i p := by
    intro i
    exact Derivation.map_neg (MvPolynomial.pderiv i) p
  have h_val : ∀ (x : Point 3) (i : Fin 3),
      polynomialValue (MvPolynomial.pderiv i (-p)) x =
      -polynomialValue (MvPolynomial.pderiv i p) x := by
    intro x i
    rw [h_pderiv i]
    exact polynomialValue_neg' (MvPolynomial.pderiv i p) x
  have h_grad : ∀ (x : Point 3),
      polynomialGradient (-p) x = -polynomialGradient p x := by
    intro x
    have h1 : (fun i : Fin 3 => polynomialValue (MvPolynomial.pderiv i (-p)) x) =
        -(fun i : Fin 3 => polynomialValue (MvPolynomial.pderiv i p) x) := by
      funext i
      exact h_val x i
    simp only [polynomialGradient, h1]
    have h2 : (EuclideanSpace.equiv (Fin 3) ℝ).symm
        (-(fun i : Fin 3 => polynomialValue (MvPolynomial.pderiv i p) x)) =
        -((EuclideanSpace.equiv (Fin 3) ℝ).symm
          (fun i : Fin 3 => polynomialValue (MvPolynomial.pderiv i p) x)) := by
      exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.map_neg _
    rw [h2]
  have h2 : ∀ (x : Point 3),
      polynomialUnitNormal (-p) x = -polynomialUnitNormal p x := by
    intro x
    have hgrad : polynomialGradient (-p) x = -polynomialGradient p x := h_grad x
    have hnorm : ‖polynomialGradient (-p) x‖ = ‖polynomialGradient p x‖ := by
      rw [hgrad, norm_neg]
    by_cases h : ‖polynomialGradient p x‖ = 0
    · have h' : ‖polynomialGradient (-p) x‖ = 0 := by rw [hnorm, h]
      simp [polynomialUnitNormal, h, h']
    · have h' : ‖polynomialGradient (-p) x‖ ≠ 0 := by
        rw [hnorm]; exact h
      have h_pos : ‖polynomialGradient (-p) x‖⁻¹ • polynomialGradient (-p) x =
          -‖polynomialGradient p x‖⁻¹ • polynomialGradient p x := by
        simp [hgrad, smul_neg]
      simp [polynomialUnitNormal, h, h', h_pos]
  have h3 : ∀ (x : Point 3),
      ‖inner ℝ e (polynomialUnitNormal (-p) x)‖ =
      ‖inner ℝ e (polynomialUnitNormal p x)‖ := by
    intro x
    rw [h2 x]
    have h4 : inner ℝ e (-polynomialUnitNormal p x) =
        -inner ℝ e (polynomialUnitNormal p x) := by
      rw [inner_neg_right]
    rw [h4, norm_neg]
  have h4 : (fun x : Point 3 => ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal (-p) x)‖) =
      (fun x : Point 3 => ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖) := by
    funext x
    rw [h3 x]
  rw [directionalSurfaceArea, directionalSurfaceArea, h4]

/-- The parameter polynomial is odd in the coefficient vector. -/
lemma parameterPolynomial_neg' {k : ℕ} (P : PolynomialParameterization k)
    (x : CoefficientSpace P.dim) :
    parameterPolynomial P (-x) = -parameterPolynomial P x := by
  have h1 : P.equiv (-x) = -P.equiv x := map_neg P.equiv x
  dsimp only [parameterPolynomial]
  exact congr_arg (fun p : degreeLESubmodule k => (p : MvPolynomial (Fin 3) ℝ)) h1

/-- The coefficient surface functional is even in the coefficient vector. -/
lemma coefficientSurfaceFunctional_even
    {k : ℕ} (P : PolynomialParameterization k)
    (u : Point 3) (U : Set (Point 3))
    (x : CoefficientSpace P.dim) :
    coefficientSurfaceFunctional P u U (-x) =
    coefficientSurfaceFunctional P u U x := by
  have h_poly : parameterPolynomial P (-x) = -parameterPolynomial P x :=
    parameterPolynomial_neg' P x
  let p := parameterPolynomial P x
  have h_poly2 : parameterPolynomial P (-x) = -p := h_poly
  have h_zeroSet2 : polynomialZeroSet (-p) = polynomialZeroSet p := by
    ext y
    simp only [polynomialZeroSet, Set.mem_setOf_eq]
    have h_val : polynomialValue (-p) y = -polynomialValue p y := polynomialValue_neg' p y
    rw [h_val]
    simp
  have h_main : directionalSurfaceArea u (-p) (polynomialZeroSet (-p) ∩ U) =
      directionalSurfaceArea u p (polynomialZeroSet p ∩ U) := by
    rw [h_zeroSet2]
    exact directionalSurfaceArea_neg_polynomial u p (polynomialZeroSet p ∩ U)
  simp only [coefficientSurfaceFunctional]
  rw [h_poly2]
  exact congr_arg ENNReal.toReal h_main

/-- Ball averaging of an even function is even. -/
lemma ballAverage_even {N : ℕ} {ε : ℝ} {f : CoefficientSpace N → ℝ}
    (_hε : 0 < ε) (hf : ∀ x, f (-x) = f x) (x : CoefficientSpace N) :
    ballAverage ε f (-x) = ballAverage ε f x := by
  let neg : CoefficientSpace N → CoefficientSpace N := fun y => -y
  have h_ball : Metric.ball (-x) ε = neg '' Metric.ball x ε := by
    ext y
    simp only [Metric.mem_ball, Set.mem_image, dist_eq_norm]
    constructor
    · intro h
      refine ⟨-y, ?_, by exact neg_neg y⟩
      have h' : ‖(-y) - x‖ < ε := by
        have h3 : (-y) - x = -(y - (-x)) := by abel
        rw [h3, norm_neg]
        exact h
      exact h'
    · rintro ⟨z, hz, rfl⟩
      have h' : ‖(-z) - (-x)‖ < ε := by
        have h3 : (-z) - (-x) = -(z - x) := by abel
        rw [h3, norm_neg]
        exact hz
      exact h'
  have h_mp : MeasurePreserving neg := Measure.measurePreserving_neg volume
  have h_emb : MeasurableEmbedding neg := measurableEmbedding_neg
  have h_integral : ∫ y in neg '' Metric.ball x ε, f y =
      ∫ y in Metric.ball x ε, f (neg y) :=
    h_mp.setIntegral_image_emb h_emb f (Metric.ball x ε)
  have h_main : ∫ y in Metric.ball (-x) ε, f y = ∫ y in Metric.ball x ε, f y := by
    rw [h_ball, h_integral]
    have h_eq : (fun y : CoefficientSpace N => f (neg y)) = f := by
      funext y
      simpa [neg] using hf y
    rw [h_eq]
  rw [ballAverage, ballAverage, h_main]

/-- The concrete mollified visibility body is antipodally even in the
coefficient vector. -/
lemma concreteMollifiedVisibilityBody_even
    {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (hε : 0 < ε) (U : Set (Point 3))
    (x : CoefficientSpace P.dim) :
    concreteMollifiedVisibilityBody P ε (-x) U =
    concreteMollifiedVisibilityBody P ε x U := by
  have h_area : ∀ (u : Point 3),
      concreteMollifiedDirectionalArea P ε (-x) u U =
      concreteMollifiedDirectionalArea P ε x u U := by
    intro u
    exact ballAverage_even hε (coefficientSurfaceFunctional_even P u U) x
  ext u
  simp only [concreteMollifiedVisibilityBody, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h_area u]

/-- For any `0 < v ≤ M`, there exists a natural number `r` such that
`2^(-r-1) * M < v ≤ 2^(-r) * M`. -/
lemma exists_dyadic_layer (v M : ℝ) (hv_pos : 0 < v) (hv_le : v ≤ M) :
    ∃ (r : ℕ), Real.rpow 2 (-(r : ℝ) - 1) * M < v ∧
      v ≤ Real.rpow 2 (-(r : ℝ)) * M := by
  have hM_pos : 0 < M := by linarith
  set t : ℝ := v / M with ht_def
  have ht_pos : 0 < t := by positivity
  have ht_le_one : t ≤ 1 := by
    rw [ht_def]
    exact (div_le_one hM_pos).mpr hv_le
  set s : ℝ := -Real.log t / Real.log 2 with hs_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_t_nonpos : Real.log t ≤ 0 := Real.log_nonpos (by linarith) ht_le_one
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    have h1 : 0 ≤ -Real.log t := by linarith
    exact div_nonneg h1 (by linarith)
  let r : ℕ := ⌊s⌋₊
  have hr1 : (r : ℝ) ≤ s := Nat.floor_le hs_nonneg
  have hr2 : s < (r : ℝ) + 1 := Nat.lt_floor_add_one s
  have h1 : (r : ℝ) * Real.log 2 ≤ -Real.log t := by
    calc
      (r : ℝ) * Real.log 2 ≤ s * Real.log 2 := by gcongr
      _ = -Real.log t := by
        rw [hs_def]
        field_simp [hlog2_pos.ne']
  have h2 : -Real.log t < ((r : ℝ) + 1) * Real.log 2 := by
    calc
      -Real.log t = s * Real.log 2 := by
        rw [hs_def]
        field_simp [hlog2_pos.ne']
      _ < ((r : ℝ) + 1) * Real.log 2 := by gcongr
  have h_pos1 : 0 < (2 : ℝ) := by norm_num
  have hlog_upper : Real.log t ≤ Real.log ((2 : ℝ) ^ (-(r : ℝ))) := by
    have h : Real.log ((2 : ℝ) ^ (-(r : ℝ))) = (-(r : ℝ)) * Real.log 2 := Real.log_rpow h_pos1 _
    rw [h]
    linarith
  have h_upper : t ≤ (2 : ℝ) ^ (-(r : ℝ)) := by
    exact (Real.log_le_log_iff ht_pos (by positivity)).mp hlog_upper
  have hlog_lower : Real.log ((2 : ℝ) ^ (-(r : ℝ) - 1)) < Real.log t := by
    have h : Real.log ((2 : ℝ) ^ (-(r : ℝ) - 1)) = (-(r : ℝ) - 1) * Real.log 2 := Real.log_rpow h_pos1 _
    rw [h]
    linarith
  have h_lower : (2 : ℝ) ^ (-(r : ℝ) - 1) < t := by
    exact (Real.log_lt_log_iff (by positivity) ht_pos).mp hlog_lower
  have h5 : t * M = v := by
    rw [ht_def]
    field_simp [hM_pos.ne']
  have h3 : (2 : ℝ) ^ (-(r : ℝ) - 1) * M < v := by
    have h4 : (2 : ℝ) ^ (-(r : ℝ) - 1) * M < t * M := by gcongr
    rw [h5] at h4
    exact h4
  have h6 : v ≤ (2 : ℝ) ^ (-(r : ℝ)) * M := by
    have h7 : t * M ≤ (2 : ℝ) ^ (-(r : ℝ)) * M := by gcongr
    rw [h5] at h7
    exact h7
  exact ⟨r, h3, h6⟩

theorem dyadic_polynomial_badSet_decomposition
    (hBody : ConcreteMollifiedVisibilityStatement)
    (hColouring : StableEllipsoidColouringStatement) :
    DyadicPolynomialBadSetDecompositionStatement := by
  rcases hColouring with ⟨α, N, net, colour, hα, hN, hcentered, hexists, hseparation⟩
  refine ⟨α, N, net, colour, hα, hN, hcentered, hseparation, ?_⟩
  intro k P ε c M hε hM

  -- Prove unitCube c ⊆ Metric.closedBall c 1
  have h_unitCube : unitCube c ⊆ Metric.closedBall c 1 := by
    intro x hx
    have h1 : ∀ i : Fin 3, |x i - c i| ≤ 1 / 2 := hx
    have h2 : ‖x - c‖ ≤ 1 := by
      have h3 : ‖x - c‖ ^ 2 = ∑ i : Fin 3, (x i - c i) ^ 2 := by
        have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, (x i - c i) ^ 2 := by positivity
        have h_norm : ‖x - c‖ = Real.sqrt (∑ i : Fin 3, (x i - c i) ^ 2) := by
          simp [EuclideanSpace.norm_eq]
        rw [h_norm, Real.sq_sqrt h_sum_nonneg]
      have h4 : ∑ i : Fin 3, (x i - c i) ^ 2 ≤ 3 / 4 := by
        have h5 : ∀ i : Fin 3, (x i - c i) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
          intro i
          have h6 : |x i - c i| ≤ 1 / 2 := h1 i
          nlinarith [abs_le.mp h6]
        have h7 : ∑ i : Fin 3, (x i - c i) ^ 2 ≤ ∑ i : Fin 3, (1 / 2 : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact h5 i
        have h8 : ∑ i : Fin 3, (1 / 2 : ℝ) ^ 2 = 3 / 4 := by norm_num
        rw [h8] at h7
        exact h7
      nlinarith
    exact h2
  have h_unitCube_meas : MeasurableSet (unitCube c) :=
    unitCube_measurableSet c

  -- Define subtype of centrally symmetric convex bodies
  let SymBody : Type _ :=
    {K : Set (Point 3) // JohnEllipsoid.IsConvexBody K ∧ (∀ x, x ∈ K → -x ∈ K)}

  -- Use choice to get a selection function
  have h_choice : ∀ (K : SymBody), ∃ (E : EllipsoidParameter),
      E ∈ net ∧ AreHomotheticallyCloseAt 0 α K.val (ellipsoidCarrier E) := by
    intro K
    exact hexists K.val K.property.1 K.property.2
  choose f hf using h_choice

  -- Define selected
  let selected : CoefficientSpace P.dim → EllipsoidParameter := fun x =>
    f ⟨concreteMollifiedVisibilityBody P ε x (unitCube c),
      hBody k P (unitCube c) c ε x h_unitCube_meas h_unitCube hε⟩

  -- Prove selected (-x) = selected x
  have h_even : ∀ (x : CoefficientSpace P.dim), selected (-x) = selected x := by
    intro x
    have h_body : concreteMollifiedVisibilityBody P ε (-x) (unitCube c) =
        concreteMollifiedVisibilityBody P ε x (unitCube c) :=
      concreteMollifiedVisibilityBody_even P ε hε (unitCube c) x
    have h_subtype :
        (⟨concreteMollifiedVisibilityBody P ε (-x) (unitCube c),
          hBody k P (unitCube c) c ε (-x) h_unitCube_meas h_unitCube hε⟩ : SymBody) =
        (⟨concreteMollifiedVisibilityBody P ε x (unitCube c),
          hBody k P (unitCube c) c ε x h_unitCube_meas h_unitCube hε⟩ : SymBody) := by
      apply Subtype.ext
      exact h_body
    dsimp only [selected]
    rw [h_subtype]

  -- Prove closeness property
  have h_close : ∀ (x : CoefficientSpace P.dim),
      x ∈ concretePolynomialBadSet P ε (unitCube c) M →
      0 < concreteMollifiedVisibility P ε x (unitCube c) →
      selected x ∈ net ∧
        AreHomotheticallyCloseAt 0 α
          (concreteMollifiedVisibilityBody P ε x (unitCube c))
          (ellipsoidCarrier (selected x)) := by
    intro x _ _
    exact hf ⟨concreteMollifiedVisibilityBody P ε x (unitCube c),
      hBody k P (unitCube c) c ε x h_unitCube_meas h_unitCube hε⟩

  -- Dyadic decomposition equality
  have h_decomposition :
      {x | x ∈ concretePolynomialBadSet P ε (unitCube c) M ∧
        0 < concreteMollifiedVisibility P ε x (unitCube c)} =
      ⋃ r : ℕ, ⋃ θ : Fin N,
        {x | x ∈ concretePolynomialBadLayer P ε (unitCube c) M r ∧
          colour (selected x) = θ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · -- Forward direction
      rintro ⟨h_bad, h_pos⟩
      have h_le : concreteMollifiedVisibility P ε x (unitCube c) ≤ M := h_bad
      have h_pos' : 0 < concreteMollifiedVisibility P ε x (unitCube c) := h_pos
      obtain ⟨r, hr1, hr2⟩ := exists_dyadic_layer
          (concreteMollifiedVisibility P ε x (unitCube c)) M h_pos' h_le
      refine ⟨r, colour (selected x), ?_⟩
      exact ⟨⟨hr1, hr2⟩, rfl⟩
    · -- Reverse direction
      rintro ⟨r, θ, ⟨hr1, hr2⟩, _⟩
      have h_pos : 0 < concreteMollifiedVisibility P ε x (unitCube c) := by
        have h_rpow_pos : 0 < Real.rpow 2 (-(r : ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
        have h : 0 < Real.rpow 2 (-(r : ℝ) - 1) * M := mul_pos h_rpow_pos hM
        linarith
      have h_le : concreteMollifiedVisibility P ε x (unitCube c) ≤ M := by
        have h : Real.rpow 2 (-(r : ℝ)) * M ≤ M := by
          have h2 : Real.rpow 2 (-(r : ℝ)) ≤ 1 := by
            have h3 : (r : ℝ) ≥ 0 := by positivity
            have h4 : Real.rpow 2 (-(r : ℝ)) ≤ Real.rpow 2 0 := by
              apply Real.rpow_le_rpow_of_exponent_le <;> norm_num
            simpa using h4
          nlinarith
        linarith
      exact ⟨h_le, h_pos⟩

  exact ⟨selected, h_even, h_close, h_decomposition⟩

end Kakeya.CV
