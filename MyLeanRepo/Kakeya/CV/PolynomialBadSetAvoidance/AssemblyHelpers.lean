import MyLeanRepo.Kakeya.CV.PolynomialBadSetAvoidance.Helpers
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Polynomial bad-set assembly helpers

Closed geometric, determinant, threshold, and sphere-transport lemmas used by
the final polynomial bad-set avoidance assembly.
-/

noncomputable section

open MeasureTheory TopCat Set Finset Filter
open scoped BigOperators ENNReal NNReal Real

namespace Kakeya.CV

/-- Every translated scaled ellipsoid is compact. -/
lemma scaledEllipsoid_isCompact
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    IsCompact (scaledEllipsoid A η z) := by
  have hball : IsCompact (Metric.closedBall (0 : Point 3) η) :=
    isCompact_closedBall _ _
  have hlinear : IsCompact (A '' Metric.closedBall (0 : Point 3) η) :=
    hball.image A.toContinuousLinearEquiv.continuous
  have htranslate : Continuous (fun y : Point 3 => z + y) :=
    continuous_const_add _
  have hset : scaledEllipsoid A η z =
      (fun y : Point 3 => z + y) ''
        (A '' Metric.closedBall (0 : Point 3) η) := by
    rfl
  rw [hset]
  exact hlinear.image htranslate

/-- Every translated scaled ellipsoid is measurable. -/
lemma scaledEllipsoid_measurableSet
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    MeasurableSet (scaledEllipsoid A η z) :=
  (scaledEllipsoid_isCompact A η z).isClosed.measurableSet

/-- Every translated scaled ellipsoid has finite volume. -/
lemma scaledEllipsoid_volume_lt_top
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    volume (scaledEllipsoid A η z) < ⊤ :=
  (scaledEllipsoid_isCompact A η z).isBounded.measure_lt_top

/-- Equal centered John ellipsoids have equal scaled translates. -/
lemma scaledEllipsoid_eq_of_ellipsoid_eq
    {A A' : Point 3 ≃ₗ[ℝ] Point 3} {η : ℝ} (hη : 0 < η)
    (h : JohnEllipsoid.ellipsoid (0 : Point 3) A =
      JohnEllipsoid.ellipsoid (0 : Point 3) A') :
    ∀ z : Point 3, scaledEllipsoid A η z = scaledEllipsoid A' η z := by
  have hsmul :
      (fun y : Point 3 => η • y) '' Metric.closedBall (0 : Point 3) 1 =
        Metric.closedBall (0 : Point 3) η := by
    ext x
    simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hnorm : ‖η • y‖ = η * ‖y‖ := by
        have h₁ : ‖η • y‖ = ‖η‖ * ‖y‖ := norm_smul η y
        have h₂ : ‖η‖ = η := by
          simpa [Real.norm_eq_abs] using abs_of_pos hη
        rw [h₁, h₂]
      rw [hnorm]
      simpa using mul_le_mul_of_nonneg_left hy hη.le
    · intro hx
      let y : Point 3 := η⁻¹ • x
      have hy : ‖y‖ ≤ 1 := by
        have hnorm : ‖y‖ = η⁻¹ * ‖x‖ := by
          simp [y, norm_smul, abs_of_pos hη]
        rw [hnorm]
        have hle :
            η⁻¹ * ‖x‖ ≤ η⁻¹ * η :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        simpa [hη.ne'] using hle
      have heq : η • y = x := by
        rw [show η • y = (η * η⁻¹) • x by simp [y, smul_smul]]
        simp [hη.ne']
      exact ⟨y, hy, heq⟩
  have hscale : ∀ B : Point 3 ≃ₗ[ℝ] Point 3,
      B '' Metric.closedBall (0 : Point 3) η =
        (fun y : Point 3 => η • y) ''
          (B '' Metric.closedBall (0 : Point 3) 1) := by
    intro B
    have himage :
        B '' ((fun y : Point 3 => η • y) ''
            Metric.closedBall (0 : Point 3) 1) =
          (fun y : Point 3 => η • y) ''
            (B '' Metric.closedBall (0 : Point 3) 1) := by
      rw [Set.image_image, Set.image_image]
      apply congr_arg
        (fun f : Point 3 → Point 3 =>
          f '' Metric.closedBall (0 : Point 3) 1)
      funext y
      exact B.map_smul η y
    rw [hsmul] at himage
    exact himage
  have hA :
      JohnEllipsoid.ellipsoid (0 : Point 3) A =
        A '' Metric.closedBall (0 : Point 3) 1 := by
    unfold JohnEllipsoid.ellipsoid
    ext y
    simp [Set.mem_vadd_set]
  have hA' :
      JohnEllipsoid.ellipsoid (0 : Point 3) A' =
        A' '' Metric.closedBall (0 : Point 3) 1 := by
    unfold JohnEllipsoid.ellipsoid
    ext y
    simp [Set.mem_vadd_set]
  have hball :
      A '' Metric.closedBall (0 : Point 3) η =
        A' '' Metric.closedBall (0 : Point 3) η := by
    rw [hscale A, hscale A', ← hA, ← hA', h]
  intro z
  unfold scaledEllipsoid
  rw [hball]

/-- Absolute determinant of an ellipsoid represented by principal axes. -/
lemma determinant_ellipsoid
    (E : Point 3 ≃ₗ[ℝ] Point 3)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ)
    (hℓ_pos : ∀ i, 0 < ℓ i)
    (hℓ_rep :
      ∀ i, E (EuclideanSpace.basisFun (Fin 3) ℝ i) = ℓ i • b i) :
    |LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3)| =
      ∏ i : Fin 3, ℓ i := by
  let e : OrthonormalBasis (Fin 3) ℝ (Point 3) :=
    EuclideanSpace.basisFun (Fin 3) ℝ
  have hdet :
      e.toBasis.det
          (fun i => (E : Point 3 →ₗ[ℝ] Point 3) (e.toBasis i)) =
        LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3) := by
    have hcomp :
        e.toBasis.det
            ((E : Point 3 →ₗ[ℝ] Point 3) ∘ e.toBasis) =
          LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3) *
            e.toBasis.det e.toBasis :=
      Module.Basis.det_comp e.toBasis
        (E : Point 3 →ₗ[ℝ] Point 3) e.toBasis
    have hself : e.toBasis.det e.toBasis = 1 :=
      Module.Basis.det_self e.toBasis
    have hcomp' :
        e.toBasis.det
            ((E : Point 3 →ₗ[ℝ] Point 3) ∘ e.toBasis) =
          LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3) := by
      rw [hcomp, hself]
      ring
    have hfun :
        ((E : Point 3 →ₗ[ℝ] Point 3) ∘ e.toBasis) =
          fun i => (E : Point 3 →ₗ[ℝ] Point 3) (e.toBasis i) := by
      funext i
      rfl
    rw [hfun] at hcomp'
    exact hcomp'
  have haxes :
      e.toBasis.det
          (fun i => (E : Point 3 →ₗ[ℝ] Point 3) (e.toBasis i)) =
        e.toBasis.det (fun i => ℓ i • b i) := by
    apply congr_arg e.toBasis.det
    funext i
    exact hℓ_rep i
  have hsmul :
      e.toBasis.det (fun i => ℓ i • b i) =
        (∏ i : Fin 3, ℓ i) * e.toBasis.det b :=
    AlternatingMap.map_smul_univ e.toBasis.det ℓ b
  have habs : |e.toBasis.det b| = 1 := by
    rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real e b with
      h | h <;> rw [h] <;> norm_num
  have hprod : 0 < ∏ i : Fin 3, ℓ i := by
    apply Finset.prod_pos
    intro i _
    exact hℓ_pos i
  calc
    |LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3)|
        = |e.toBasis.det
            (fun i =>
              (E : Point 3 →ₗ[ℝ] Point 3) (e.toBasis i))| := by
          rw [hdet]
    _ = |e.toBasis.det (fun i => ℓ i • b i)| := by rw [haxes]
    _ = |(∏ i : Fin 3, ℓ i) * e.toBasis.det b| := by rw [hsmul]
    _ = (∏ i : Fin 3, ℓ i) * |e.toBasis.det b| := by
      rw [abs_mul, abs_of_pos hprod]
    _ = ∏ i : Fin 3, ℓ i := by rw [habs, mul_one]

/-- Volume of a scaled ellipsoid represented by principal axes. -/
lemma volume_scaledEllipsoid_determinant
    (E : Point 3 ≃ₗ[ℝ] Point 3)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ)
    (hℓ_pos : ∀ i, 0 < ℓ i)
    (hℓ_rep :
      ∀ i, E (EuclideanSpace.basisFun (Fin 3) ℝ i) = ℓ i • b i)
    (η : ℝ) (hη : 0 < η) (z : Point 3) :
    volume (scaledEllipsoid E η z) =
      ENNReal.ofReal (η ^ 3 * ∏ i : Fin 3, ℓ i) *
        volume (unitBall 3) := by
  have hdet :
      |LinearMap.det (E : Point 3 →ₗ[ℝ] Point 3)| =
        ∏ i : Fin 3, ℓ i :=
    determinant_ellipsoid E b ℓ hℓ_pos hℓ_rep
  rw [volume_affine_ball E η hη z, hdet]

/-- Specialize the global many-bisections scale threshold to a unit cube. -/
lemma eta_small_manyBisects
    (C_mb C_pack : ℝ≥0) (α : ℝ) (c : Point 3)
    (sphereArea denom threshold : ENNReal)
    (hthreshold_eq : threshold = sphereArea / denom)
    (hsphereArea_eq :
      sphereArea = codimensionOneMeasure 3 (unitSphere 3))
    (hdenom_eq :
      denom =
        (3 : ℝ≥0∞) * (C_mb : ℝ≥0∞) * ENNReal.ofReal α *
          (C_pack : ℝ≥0∞) * volume (unitBall 3))
    (η : ℝ) (hη_small : ENNReal.ofReal η < threshold) :
    ENNReal.ofReal η <
      manyBisectsThreshold C_mb C_pack α (unitCube c) := by
  have hcube : volume (unitCube c) = (1 : ENNReal) := by
    exact_mod_cast volume_unitCube c
  have heq :
      manyBisectsThreshold C_mb C_pack α (unitCube c) =
        threshold := by
    dsimp only [manyBisectsThreshold]
    rw [hcube, one_mul, ← hsphereArea_eq, ← hdenom_eq]
    exact hthreshold_eq.symm
  rw [heq]
  exact hη_small

/-- Transport antipodal separation from ambient coefficient space to the
standard parameter sphere. -/
lemma sphere_separation_from_ambient
    {k : ℕ} {P : PolynomialParameterization k}
    (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
    (D : Set (CoefficientSpace P.dim))
    (hD : D ⊆ normalizedPolynomialParameters P)
    (h : normalizedPolynomialParameters P ≃ₜ
      TopCat.sphere (P.dim - 1))
    (hantipodal :
      ∀ x : normalizedPolynomialParameters P,
        h (normalizedParameterAntipodal P x) =
          TopCat.sphereAntipodal (P.dim - 1) (h x))
    (hsep :
      positiveSignClass P selectedRegion D ∩
        closure ((fun x : CoefficientSpace P.dim => -x) ''
          positiveSignClass P selectedRegion D) = ∅) :
    h '' {x : normalizedPolynomialParameters P |
        (x : CoefficientSpace P.dim) ∈
          positiveSignClass P selectedRegion D} ∩
      closure (TopCat.sphereAntipodal (P.dim - 1) ''
        (h '' {x : normalizedPolynomialParameters P |
          (x : CoefficientSpace P.dim) ∈
            positiveSignClass P selectedRegion D})) = ∅ := by
  let A : Set (normalizedPolynomialParameters P) :=
    {x | (x : CoefficientSpace P.dim) ∈
      positiveSignClass P selectedRegion D}
  let neg :
      normalizedPolynomialParameters P →
        normalizedPolynomialParameters P :=
    normalizedParameterAntipodal P
  have hsub :
      positiveSignClass P selectedRegion D ⊆
        normalizedPolynomialParameters P := by
    intro x hx
    exact hD hx.1
  have himage :
      Subtype.val '' (neg '' A) =
        (fun x : CoefficientSpace P.dim => -x) ''
          positiveSignClass P selectedRegion D := by
    ext z
    simp only [A, neg, Set.mem_image, Set.mem_setOf_eq,
      normalizedParameterAntipodal]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      let x' : normalizedPolynomialParameters P := ⟨x, hsub hx⟩
      have hx' : x' ∈ A := hx
      have hneg : (neg x' : CoefficientSpace P.dim) = -x := by
        change -(x' : CoefficientSpace P.dim) = -x
        change -x = -x
        rfl
      exact ⟨neg x', ⟨x', hx', rfl⟩, hneg⟩
  have hA : A ∩ closure (neg '' A) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have hinducing :
        Topology.IsInducing
          (Subtype.val :
            normalizedPolynomialParameters P →
              CoefficientSpace P.dim) :=
      Topology.IsInducing.subtypeVal
    have hclosure :
        (y : CoefficientSpace P.dim) ∈
          closure (Subtype.val '' (neg '' A)) := by
      have heq :
          closure (neg '' A) =
            Subtype.val ⁻¹' closure (Subtype.val '' (neg '' A)) :=
        hinducing.closure_eq_preimage_closure_image (neg '' A)
      rw [heq] at hy
      exact hy.2
    rw [himage] at hclosure
    have :
        (y : CoefficientSpace P.dim) ∈
          positiveSignClass P selectedRegion D ∩
            closure ((fun x : CoefficientSpace P.dim => -x) ''
              positiveSignClass P selectedRegion D) :=
      ⟨hy.1, hclosure⟩
    rw [hsep] at this
    exact this
  exact transport_separation h hantipodal hA

/-- Transport an ambient antipodal bad-set cover to the standard parameter
sphere. -/
lemma sphere_cover_from_ambient
    {k : ℕ} {P : PolynomialParameterization k} {I : Type*}
    (selectedRegion :
      I → CoefficientSpace P.dim → Set (Point 3))
    (D : I → Set (CoefficientSpace P.dim))
    (hD : ∀ i, D i ⊆ normalizedPolynomialParameters P)
    (bad : Set (CoefficientSpace P.dim))
    (h : normalizedPolynomialParameters P ≃ₜ
      TopCat.sphere (P.dim - 1))
    (hantipodal :
      ∀ x : normalizedPolynomialParameters P,
        h (normalizedParameterAntipodal P x) =
          TopCat.sphereAntipodal (P.dim - 1) (h x))
    (hcover :
      bad ⊆ ⋃ i : I,
        positiveSignClass P (selectedRegion i) (D i) ∪
          (fun x : CoefficientSpace P.dim => -x) ''
            positiveSignClass P (selectedRegion i) (D i)) :
    h '' {x : normalizedPolynomialParameters P |
        (x : CoefficientSpace P.dim) ∈ bad} ⊆
      ⋃ i : I,
        h '' {x : normalizedPolynomialParameters P |
            (x : CoefficientSpace P.dim) ∈
              positiveSignClass P (selectedRegion i) (D i)} ∪
          TopCat.sphereAntipodal (P.dim - 1) ''
            (h '' {x : normalizedPolynomialParameters P |
              (x : CoefficientSpace P.dim) ∈
                positiveSignClass P (selectedRegion i) (D i)}) := by
  let A : I → Set (normalizedPolynomialParameters P) := fun i =>
    {x | (x : CoefficientSpace P.dim) ∈
      positiveSignClass P (selectedRegion i) (D i)}
  let bad' : Set (normalizedPolynomialParameters P) :=
    {x | (x : CoefficientSpace P.dim) ∈ bad}
  let neg :
      normalizedPolynomialParameters P →
        normalizedPolynomialParameters P :=
    normalizedParameterAntipodal P
  have hsub :
      ∀ i, positiveSignClass P (selectedRegion i) (D i) ⊆
        normalizedPolynomialParameters P := by
    intro i x hx
    exact hD i hx.1
  have hcover' : bad' ⊆ ⋃ i : I, A i ∪ neg '' A i := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hy)
    rcases hi with hi | hi
    · exact Set.mem_iUnion.mpr ⟨i, Or.inl hi⟩
    · obtain ⟨z, hz, heq⟩ := hi
      let z' : normalizedPolynomialParameters P := ⟨z, hsub i hz⟩
      have heq' : -z = (y : CoefficientSpace P.dim) := by
        simpa using heq
      have hneg : neg z' = y := by
        apply Subtype.ext
        have hval : (neg z' : CoefficientSpace P.dim) = -z := by
          change -(z' : CoefficientSpace P.dim) = -z
          change -z = -z
          rfl
        rw [hval]
        exact heq'
      exact Set.mem_iUnion.mpr
        ⟨i, Or.inr ⟨z', hz, hneg⟩⟩
  exact transport_cover h hantipodal hcover'

/-- A finite supremum of natural-valued terms is bounded in `ℝ≥0` when every
term is bounded. -/
lemma finset_sup_cast_le
    {α : Type*} {s : Finset α} {f : α → ℕ} {bound : ℝ≥0}
    (hs : s.Nonempty)
    (h : ∀ x ∈ s, (f x : ℝ≥0) ≤ bound) :
    (↑(s.sup f) : ℝ≥0) ≤ bound := by
  obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup s hs f
  rw [hsup]
  exact h x hx

/-- The cardinality of a `Fin` indexed by the supremum over an attached
finset is bounded by any pointwise `ℝ≥0` bound. -/
lemma card_fin_attached_sup_le
    {α : Type*} (s : Finset α) (f : α → ℕ) {bound : ℝ≥0}
    (h : ∀ x ∈ s, (f x : ℝ≥0) ≤ bound) :
    (Fintype.card
        (Fin (s.attach.sup (fun x => f x.1))) : ℝ≥0) ≤ bound := by
  rw [Fintype.card_fin]
  have hcoe :
      (↑(s.attach.sup (fun x => f x.1)) : ℝ≥0) =
        s.attach.sup (fun x => (f x.1 : ℝ≥0)) :=
    Nat.cast_finsetSup s.attach (fun x => f x.1)
  rw [hcoe]
  apply Finset.sup_le
  intro x hx
  exact h x.1 x.2

/-- The cardinality of a `Fin` indexed by the attached supremum of a finite
set is bounded by any pointwise `ℝ≥0` bound. The decidability argument is
explicit so this lemma can match a surrounding dependent `if` definition. -/
lemma card_fin_finite_set_sup_le
    {α : Type*} (s : Set α) (hs : s.Finite) (f : α → ℕ)
    (d : Decidable s.Nonempty) {bound : ℝ≥0}
    (h : ∀ x ∈ s, (f x : ℝ≥0) ≤ bound) :
    (Fintype.card
        (Fin (@ite ℕ s.Nonempty d
          (hs.toFinset.attach.sup (fun x => f x.1)) 0)) : ℝ≥0) ≤ bound := by
  split_ifs with hne
  · apply card_fin_attached_sup_le hs.toFinset f
    intro x hx
    exact h x (hs.mem_toFinset.mp hx)
  · simp

end Kakeya.CV
