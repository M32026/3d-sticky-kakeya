import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Additive volume bound from multiplicity + thinning

Given an original shading `Y` with per-tube density `lambda1` and a thinned
shading `Y'` with exact per-tube density `lambda2`, if the pointwise multiplicity
of `Y` is bounded by `C` and `lambda2 * C ≤ lambda1`, then the total thinned mass
fits inside the volume of `Y.union`.

Self-contained: defines `shadedMultiplicity'` and proves the mass inequality
directly via lintegral.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset Set

attribute [local instance] Classical.propDecidable

/-- Number of tubes whose shading contains x. -/
def shadedMultiplicity' {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (x : Point3) : ℕ :=
  (F.filter fun T => x ∈ Y.carrier T).card

/-- Sum of indicators equals filtered cardinality (as ENNReal). -/
private lemma sum_indicator_eq_card {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (x : Point3) :
    ∑ T ∈ F, Set.indicator (Y.carrier T) (fun _ : Point3 => (1 : ENNReal)) x =
    (shadedMultiplicity' Y x : ENNReal) := by
  let p : Kakeya.DeltaTube δ → Prop := fun T => x ∈ Y.carrier T
  have h1 : ∑ T ∈ F, Set.indicator (Y.carrier T) (fun _ : Point3 => (1 : ENNReal)) x =
      ∑ T ∈ F, (if p T then (1 : ENNReal) else 0) := by
    apply Finset.sum_congr rfl
    intro T _
    simp [Set.indicator_apply]
    <;> split_ifs <;> simp
  rw [h1]
  have h2 : ∑ T ∈ F, (if p T then (1 : ENNReal) else 0) =
      ∑ T ∈ F.filter p, (1 : ENNReal) := by
    rw [Finset.sum_ite]
    <;> simp
  rw [h2]
  simp [shadedMultiplicity', Finset.sum_const]
  <;> norm_cast

/-- Mass equals lintegral of pointwise multiplicity. -/
lemma mass_eq_lintegral_multiplicity' {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) :
    Y.mass = ∫⁻ x, (shadedMultiplicity' Y x : ENNReal) := by
  let f : Kakeya.DeltaTube δ → Point3 → ENNReal := fun T =>
    Set.indicator (Y.carrier T) (fun _ => (1 : ENNReal))
  have h1 : ∫⁻ x, (shadedMultiplicity' Y x : ENNReal) =
      ∫⁻ x, ∑ T ∈ F, f T x := by
    congr with x
    exact (sum_indicator_eq_card Y x).symm
  have h_meas : ∀ T ∈ F, Measurable (f T) := by
    intro T hT
    have hms : MeasurableSet (Y.carrier T) := Y.measurable_carrier hT
    exact measurable_const.indicator hms
  have h2 : ∫⁻ x, ∑ T ∈ F, f T x = ∑ T ∈ F, ∫⁻ x, f T x :=
    MeasureTheory.lintegral_finsetSum F h_meas
  have h3 : ∀ T ∈ F, ∫⁻ x, f T x = volume (Y.carrier T) := by
    intro T hT
    have hms : MeasurableSet (Y.carrier T) := Y.measurable_carrier hT
    rw [MeasureTheory.lintegral_indicator hms]
    <;> simp
  calc Y.mass
    = ∑ T ∈ F, volume (Y.carrier T) := by rfl
  _ = ∑ T ∈ F, ∫⁻ x, f T x := by
    apply Finset.sum_congr rfl; intro T hT; exact (h3 T hT).symm
  _ = ∫⁻ x, ∑ T ∈ F, f T x := h2.symm
  _ = ∫⁻ x, (shadedMultiplicity' Y x : ENNReal) := h1.symm

/-- `Y.union` is measurable as a finite union of measurable sets. -/
private lemma union_measurable' {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) : MeasurableSet Y.union := by
  have h : Y.union = ⋃ T ∈ F, Y.carrier T := by
    ext x
    simp [Kakeya.Shading.union, Set.mem_iUnion]
  rw [h]
  exact Finset.measurableSet_biUnion F fun T _ => Y.measurable_carrier ‹_›

/-- If pointwise multiplicity ≤ C, then mass ≤ C * volume(union). -/
lemma mass_le_C_mul_volume' {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (Y : Kakeya.Shading F) (C : ℕ)
    (hC : ∀ x, shadedMultiplicity' Y x ≤ C) :
    Y.mass ≤ (C : ENNReal) * volume Y.union := by
  rw [mass_eq_lintegral_multiplicity' Y]
  let g : Point3 → ENNReal := fun x =>
    Set.indicator Y.union (fun _ => (C : ENNReal)) x
  have h_le : ∀ x, (shadedMultiplicity' Y x : ENNReal) ≤ g x := by
    intro x
    by_cases hx : x ∈ Y.union
    · simp [g, hx, Set.indicator] <;> exact_mod_cast hC x
    · have h_not : ∀ T ∈ F, x ∉ Y.carrier T := by
        intro T hT hxT
        exact hx ⟨T, hT, hxT⟩
      have h_empty : F.filter (fun T => x ∈ Y.carrier T) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact h_not
      have h' : shadedMultiplicity' Y x = 0 := by
        rw [shadedMultiplicity', h_empty] <;> simp
      simp [g, hx, h']
  have h4 : ∫⁻ x, (shadedMultiplicity' Y x : ENNReal) ≤ ∫⁻ x, g x :=
    lintegral_mono h_le
  have h5 : ∫⁻ x, g x = (C : ENNReal) * volume Y.union := by
    rw [lintegral_indicator (union_measurable' Y)]
    <;> simp
  rw [h5] at h4
  exact h4

/-- General additive volume bound: if multiplicity ≤ C and `lambda2 * C ≤ lambda1`,
then the thinned mass is bounded by `volume Y.union`. -/
lemma additive_volume_from_multiplicity
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y Y' : Kakeya.Shading F}
    {lambda1 lambda2 : ENNReal}
    (C : ℕ) (hC_pos : 0 < C)
    (h_mult : ∀ x, shadedMultiplicity' Y x ≤ C)
    (h_thin : ∀ T ∈ F, volume (Y'.carrier T) = lambda2 * T.volume)
    (h_orig_dense : HairbrushPerTubeDense Y lambda1)
    (h_eps : lambda2 * (C : ENNReal) ≤ lambda1) :
    ∑ T ∈ F, volume (Y'.carrier T) ≤ volume Y.union := by
  have hC_ne_zero : (C : ENNReal) ≠ 0 := by
    exact_mod_cast hC_pos.ne'
  have hC_ne_top : (C : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top C
  let S : ENNReal := F.mass
  have h_mass_le : Y.mass ≤ (C : ENNReal) * volume Y.union :=
    mass_le_C_mul_volume' Y C h_mult
  have h_dense_sum : lambda1 * S ≤ Y.mass := by
    have h3 : ∀ T ∈ F, lambda1 * T.volume ≤ volume (Y.carrier T) := h_orig_dense
    have h_eq1 : lambda1 * S = ∑ T ∈ F, (lambda1 * T.volume) := by
      have h : S = ∑ T ∈ F, T.volume := by
        simp [S, Kakeya.TubeFamily.mass]
      rw [h, Finset.mul_sum]
    rw [h_eq1]
    exact Finset.sum_le_sum h3
  have h4 : (lambda2 * S) * (C : ENNReal) ≤ (volume Y.union) * (C : ENNReal) := by
    calc (lambda2 * S) * (C : ENNReal)
      = (lambda2 * (C : ENNReal)) * S := by ring
    _ ≤ lambda1 * S := mul_le_mul_of_nonneg_right h_eps (by positivity)
    _ ≤ Y.mass := h_dense_sum
    _ ≤ (C : ENNReal) * volume Y.union := h_mass_le
    _ = (volume Y.union) * (C : ENNReal) := by ring
  have h_cancel : ∀ (a b : ENNReal), a * (C : ENNReal) ≤ b * (C : ENNReal) → a ≤ b := by
    intro a b h
    have h5 : a * (C : ENNReal) * (C : ENNReal)⁻¹ ≤ b * (C : ENNReal) * (C : ENNReal)⁻¹ :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have h6 : (C : ENNReal) * (C : ENNReal)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hC_ne_zero hC_ne_top
    simpa [h6, mul_assoc] using h5
  have h5 : lambda2 * S ≤ volume Y.union := h_cancel (lambda2 * S) (volume Y.union) h4
  have h7 : ∑ T ∈ F, volume (Y'.carrier T) = lambda2 * S := by
    calc ∑ T ∈ F, volume (Y'.carrier T)
      = ∑ T ∈ F, (lambda2 * T.volume) := Finset.sum_congr rfl fun T hT => h_thin T hT
    _ = lambda2 * ∑ T ∈ F, T.volume := by rw [Finset.mul_sum]
    _ = lambda2 * S := by
      have h : S = ∑ T ∈ F, T.volume := by
        simp [S, Kakeya.TubeFamily.mass]
      rw [h]
  rw [h7]
  exact h5

end Kakeya.Assouad
