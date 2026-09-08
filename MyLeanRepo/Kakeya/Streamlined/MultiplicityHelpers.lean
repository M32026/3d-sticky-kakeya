import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Multiplicity helper lemmas

1. `refinement_mult`: a c-refinement cannot decrease average multiplicity by more than c⁻¹
2. `basic_mult_upper`: pointwise multiplicity upper bound implies average multiplicity upper bound
3. `basic_mult_lower`: pointwise multiplicity lower bound implies average multiplicity lower bound

These correspond to Lemmas `lemmarefinemult` and `lemmabasicmult` in the paper.

Whiteprint nodes: `helper-refinement-multiplicity`, `helper-basic-multiplicity`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-! ### Lemma refinemult -/

/--
If `R` is a `c`-refinement of `Y` and the refined shading has average multiplicity
at most `M`, then the original shading has average multiplicity at most `c⁻¹ * M`.
-/
lemma refinement_mult {F : BodyFamily} {Y : Shading F} {R : Refinement Y}
    {c M : ENNReal} (hc : c ≠ 0) (hct : c ≠ ⊤)
    (hR : R.RetainsMass c)
    (h : R.shading.HasAverageMultiplicityAtMost M) :
    Y.HasAverageMultiplicityAtMost (c⁻¹ * M) := by
  have h1 : c * Y.mass ≤ R.shading.mass := hR
  have h_cancel : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc hct
  have h2 : Y.mass ≤ c⁻¹ * R.shading.mass := by
    have h21 : c⁻¹ * (c * Y.mass) = Y.mass := by
      rw [← mul_assoc, h_cancel, one_mul]
    have h22 : c⁻¹ * (c * Y.mass) ≤ c⁻¹ * R.shading.mass := by gcongr
    rw [h21] at h22
    exact h22
  have h3 : R.shading.mass ≤ M * volume R.shading.union := h
  have h4 : volume R.shading.union ≤ volume Y.union := by
    apply volume.mono
    intro x hx
    rcases hx with ⟨i, hi⟩
    refine ⟨R.subfamily.embedding i, ?_⟩
    exact R.shading_subset i hi
  have h_main : Y.mass ≤ c⁻¹ * M * volume Y.union := by
    calc Y.mass
      ≤ c⁻¹ * R.shading.mass := h2
      _ ≤ c⁻¹ * (M * volume R.shading.union) := by gcongr
      _ = c⁻¹ * M * volume R.shading.union := by rw [mul_assoc]
      _ ≤ c⁻¹ * M * volume Y.union := by gcongr
  exact h_main

/--
Transfer an average-multiplicity estimate through explicit shaded-mass and
union comparisons.

This division-free form is convenient when a finite selection theorem
returns `Y.mass ≤ L * Z.mass` directly rather than packaging `Z` as a
`Refinement Y` with reciprocal retention.
-/
lemma averageMultiplicity_transfer_of_mass_union
    {F G : BodyFamily} {Y : Shading F} {Z : Shading G}
    {L M : ENNReal}
    (hmass : Y.mass ≤ L * Z.mass)
    (hunion : Z.union ⊆ Y.union)
    (hZ : Z.HasAverageMultiplicityAtMost M) :
    Y.HasAverageMultiplicityAtMost (L * M) := by
  calc
    Y.mass
        ≤ L * Z.mass := hmass
    _ ≤ L * (M * volume Z.union) := by
      exact mul_le_mul_left' hZ L
    _ = (L * M) * volume Z.union := by
      rw [mul_assoc]
    _ ≤ (L * M) * volume Y.union := by
      exact mul_le_mul_left' (volume.mono hunion) (L * M)

/--
Transfer average multiplicity from a shading appearing in a cross-multiplied
mass/union comparison.

This is the division-free form used by the direction and spatial-slab
selectors in the plank reduction.
-/
lemma averageMultiplicity_transfer_of_product
    {F G : BodyFamily} {Y : Shading F} {Z : Shading G}
    {L M : ENNReal}
    (hproduct :
      Y.mass * volume Z.union ≤
        L * Z.mass * volume Y.union)
    (hZ : Z.HasAverageMultiplicityAtMost M)
    (hZUnionZero : volume Z.union ≠ 0)
    (hZUnionTop : volume Z.union ≠ ⊤) :
    Y.HasAverageMultiplicityAtMost (L * M) := by
  have hmul :
      Y.mass * volume Z.union ≤
        (L * M * volume Y.union) *
          volume Z.union := by
    calc
      Y.mass * volume Z.union
          ≤ L * Z.mass * volume Y.union := hproduct
      _ ≤ L * (M * volume Z.union) *
          volume Y.union := by
        exact mul_le_mul_right' (mul_le_mul_left' hZ L)
          (volume Y.union)
      _ =
          (L * M * volume Y.union) *
            volume Z.union := by
        ring
  exact
    (ENNReal.mul_le_mul_iff_right
      hZUnionZero hZUnionTop).mp <| by
        simpa [mul_comm] using hmul

/--
Compose two cross-multiplied average-multiplicity comparisons.

This is the division-free form of transitivity.  The intermediate shaded
union must have positive finite volume so that it can be cancelled.
-/
lemma averageMultiplicity_product_trans
    {F G H : BodyFamily}
    {Y : Shading F} {Z : Shading G} {W : Shading H}
    {L K : ENNReal}
    (hYZ :
      Y.mass * volume Z.union ≤
        L * Z.mass * volume Y.union)
    (hZW :
      Z.mass * volume W.union ≤
        K * W.mass * volume Z.union)
    (hZUnionZero : volume Z.union ≠ 0)
    (hZUnionTop : volume Z.union ≠ ⊤) :
    Y.mass * volume W.union ≤
      (L * K) * W.mass * volume Y.union := by
  have hmul :
      (Y.mass * volume W.union) * volume Z.union ≤
        ((L * K) * W.mass * volume Y.union) *
          volume Z.union := by
    calc
      (Y.mass * volume W.union) * volume Z.union =
          (Y.mass * volume Z.union) *
            volume W.union := by ring
      _ ≤ (L * Z.mass * volume Y.union) *
            volume W.union := by gcongr
      _ = L * volume Y.union *
            (Z.mass * volume W.union) := by ring
      _ ≤ L * volume Y.union *
            (K * W.mass * volume Z.union) := by gcongr
      _ =
          ((L * K) * W.mass * volume Y.union) *
            volume Z.union := by ring
  exact
    (ENNReal.mul_le_mul_iff_right
      hZUnionZero hZUnionTop).mp <| by
        simpa [mul_comm] using hmul

/--
Restrict the right-hand shading in a cross-multiplied average-multiplicity
comparison, paying a mass-retention factor `K`.
-/
lemma averageMultiplicity_product_restrict_right
    {F G : BodyFamily}
    {Y : Shading F} {Z W : Shading G}
    {L K : ENNReal}
    (hYZ :
      Y.mass * volume Z.union ≤
        L * Z.mass * volume Y.union)
    (hmass : Z.mass ≤ K * W.mass)
    (hunion : W.union ⊆ Z.union)
    (hZUnionZero : volume Z.union ≠ 0)
    (hZUnionTop : volume Z.union ≠ ⊤) :
    Y.mass * volume W.union ≤
      (L * K) * W.mass * volume Y.union := by
  have hZW :
      Z.mass * volume W.union ≤
        K * W.mass * volume Z.union := by
    calc
      Z.mass * volume W.union
          ≤ (K * W.mass) * volume W.union := by gcongr
      _ ≤ K * W.mass * volume Z.union := by
        gcongr
  exact averageMultiplicity_product_trans
    hYZ hZW hZUnionZero hZUnionTop

lemma averageMultiplicity_product_trans_two
    {F G H : BodyFamily}
    {Y : Shading F} {Z : Shading G} {W : Shading H}
    {L : ENNReal}
    (hYZ :
      Y.mass * volume Z.union ≤
        L * Z.mass * volume Y.union)
    (hZW :
      Z.mass * volume W.union ≤
        2 * W.mass * volume Z.union)
    (hZUnionZero : volume Z.union ≠ 0)
    (hZUnionTop : volume Z.union ≠ ⊤) :
    Y.mass * volume W.union ≤
      (2 * L) * W.mass * volume Y.union := by
  have h :=
    averageMultiplicity_product_trans
      hYZ hZW hZUnionZero hZUnionTop
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-! ### Lemma basicmult -/

/-- The union of a shading is a finite union of measurable sets, hence measurable. -/
lemma Shading.union_measurable {F : BodyFamily} (Y : Shading F) :
    MeasurableSet Y.union := by
  have h : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
    ext x
    simp [Shading.union]
  rw [h]
  exact MeasurableSet.iUnion (fun i => Y.measurable_carrier i)

/-- The pointwise multiplicity equals the sum of indicator functions. -/
lemma pointMultiplicity_eq_sum_indicators {F : BodyFamily} (Y : Shading F)
    (x : Point3) :
    (Y.pointMultiplicity x : ENNReal) =
      ∑ i : Fin F.card, Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x := by
  classical
  simp [Shading.pointMultiplicity, Set.indicator_apply]

/--
The lintegral of the pointwise multiplicity equals the total shaded mass.

Key identity: `∫ μ(x) dx = ∑ |Y_i|`.
-/
lemma lintegral_pointMultiplicity_eq_mass {F : BodyFamily} (Y : Shading F) :
    ∫⁻ x : Point3, (Y.pointMultiplicity x : ENNReal) = Y.mass := by
  have h1 : (fun x : Point3 => (Y.pointMultiplicity x : ENNReal)) =
      fun x : Point3 => ∑ i : Fin F.card,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x := by
    funext x
    exact pointMultiplicity_eq_sum_indicators Y x
  rw [h1]
  have h3 : ∫⁻ x : Point3, ∑ i : Fin F.card,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x =
      ∑ i : Fin F.card, ∫⁻ x : Point3,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x := by
    apply MeasureTheory.lintegral_finsetSum
    intro i _
    exact Measurable.indicator (by fun_prop) (Y.measurable_carrier i)
  rw [h3]
  have h4 : ∀ i : Fin F.card, ∫⁻ x : Point3,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x =
      volume (Y.carrier i) := by
    intro i
    rw [MeasureTheory.lintegral_indicator (Y.measurable_carrier i)]
    exact MeasureTheory.setLIntegral_one (Y.carrier i)
  have h5 : ∑ i : Fin F.card, ∫⁻ x : Point3,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x =
      ∑ i : Fin F.card, volume (Y.carrier i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h4 i
  rw [h5]
  rfl

/-- The pointwise multiplicity function (as ENNReal) is measurable. -/
lemma Shading.pointMultiplicity_measurable {F : BodyFamily} (Y : Shading F) :
    Measurable (fun x : Point3 => (Y.pointMultiplicity x : ENNReal)) := by
  have h1 : (fun x : Point3 => (Y.pointMultiplicity x : ENNReal)) =
      fun x : Point3 => ∑ i : Fin F.card,
        Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal)) x := by
    funext x
    exact pointMultiplicity_eq_sum_indicators Y x
  rw [h1]
  exact Finset.measurable_sum (Finset.univ)
    (fun i _ => Measurable.indicator (by fun_prop) (Y.measurable_carrier i))

/-- If x is not in the shaded union, the pointwise multiplicity is zero. -/
lemma pointMultiplicity_zero_outside_union {F : BodyFamily} (Y : Shading F)
    {x : Point3} (hx : x ∉ Y.union) : Y.pointMultiplicity x = 0 := by
  classical
  have h6 : ∀ (i : Fin F.card), x ∉ Y.carrier i := by
    intro i h7
    have h8 : x ∈ Y.union := ⟨i, h7⟩
    exact hx h8
  have h9 : (Finset.univ.filter fun i : Fin F.card => x ∈ Y.carrier i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact fun i _ => h6 i
  simp [Shading.pointMultiplicity, h9]

/--
Pointwise multiplicity upper bound implies average multiplicity upper bound.
-/
lemma basic_mult_upper {F : BodyFamily} {Y : Shading F} {M : ENNReal}
    (h : ∀ x ∈ Y.union, (Y.pointMultiplicity x : ENNReal) ≤ M) :
    Y.HasAverageMultiplicityAtMost M := by
  have h1 : ∀ (x : Point3), (Y.pointMultiplicity x : ENNReal) ≤ M := by
    intro x
    by_cases hx : x ∈ Y.union
    · exact h x hx
    · have h2 : Y.pointMultiplicity x = 0 := pointMultiplicity_zero_outside_union Y hx
      rw [h2]
      simp
  let f : Point3 → ENNReal := fun x => (Y.pointMultiplicity x : ENNReal)
  have h_ind : f = Set.indicator Y.union f := by
    funext x
    by_cases hx : x ∈ Y.union
    · simp [hx, f]
    · have hz : Y.pointMultiplicity x = 0 := pointMultiplicity_zero_outside_union Y hx
      simp [hx, hz, f]
  have h10 : ∫⁻ x : Point3, f x = ∫⁻ x : Point3, Set.indicator Y.union f x :=
    congr_arg (fun g : Point3 → ENNReal => ∫⁻ x, g x) h_ind
  have h_eq : ∫⁻ x : Point3, f x = ∫⁻ x : Point3 in Y.union, f x := by
    rw [h10]
    exact MeasureTheory.lintegral_indicator (Y.union_measurable) f
  have h_bound : ∫⁻ x : Point3 in Y.union, f x ≤ M * volume Y.union := by
    have h5 : ∫⁻ x : Point3 in Y.union, f x ≤ ∫⁻ x : Point3 in Y.union, M := by
      apply MeasureTheory.setLIntegral_mono' (Y.union_measurable)
      exact fun x _ => h1 x
    rw [MeasureTheory.setLIntegral_const] at h5
    exact h5
  have h_final : Y.mass ≤ M * volume Y.union := by
    have h_mass : (∫⁻ x : Point3, f x) = Y.mass := lintegral_pointMultiplicity_eq_mass Y
    rw [← h_mass, h_eq]
    exact h_bound
  exact h_final

/--
Pointwise multiplicity lower bound implies average multiplicity lower bound.
-/
lemma basic_mult_lower {F : BodyFamily} {Y : Shading F} {m : ENNReal}
    (h : ∀ x ∈ Y.union, m ≤ (Y.pointMultiplicity x : ENNReal)) :
    m * volume Y.union ≤ Y.mass := by
  let f : Point3 → ENNReal := fun x => (Y.pointMultiplicity x : ENNReal)
  have h_ind : f = Set.indicator Y.union f := by
    funext x
    by_cases hx : x ∈ Y.union
    · simp [hx, f]
    · have hz : Y.pointMultiplicity x = 0 := pointMultiplicity_zero_outside_union Y hx
      simp [hx, hz, f]
  have h10 : ∫⁻ x : Point3, f x = ∫⁻ x : Point3, Set.indicator Y.union f x :=
    congr_arg (fun g : Point3 → ENNReal => ∫⁻ x, g x) h_ind
  have h_eq : ∫⁻ x : Point3, f x = ∫⁻ x : Point3 in Y.union, f x := by
    rw [h10]
    exact MeasureTheory.lintegral_indicator (Y.union_measurable) f
  have h_mass : (∫⁻ x : Point3, f x) = Y.mass := lintegral_pointMultiplicity_eq_mass Y
  have h_bound : m * volume Y.union ≤ ∫⁻ x : Point3 in Y.union, f x := by
    have h5 : ∫⁻ x : Point3 in Y.union, m ≤ ∫⁻ x : Point3 in Y.union, f x := by
      apply MeasureTheory.setLIntegral_mono' (Y.union_measurable)
      exact fun x _ => h x ‹_›
    rw [MeasureTheory.setLIntegral_const] at h5
    exact h5
  calc m * volume Y.union
    ≤ ∫⁻ x : Point3 in Y.union, f x := h_bound
    _ = ∫⁻ x : Point3, f x := h_eq.symm
    _ = Y.mass := h_mass

/--
Monotonicity of average multiplicity: if the bound holds for `M₁` and
`M₁ ≤ M₂`, then it holds for `M₂`.
-/
lemma Shading.HasAverageMultiplicityAtMost.mono {F : BodyFamily}
    {Y : Shading F} {M₁ M₂ : ENNReal}
    (h : Y.HasAverageMultiplicityAtMost M₁) (hM : M₁ ≤ M₂) :
    Y.HasAverageMultiplicityAtMost M₂ := by
  have h1 : Y.mass ≤ M₁ * volume Y.union := h
  have h2 : M₁ * volume Y.union ≤ M₂ * volume Y.union := by
    gcongr
  exact le_trans h1 h2

end Kakeya.Streamlined
