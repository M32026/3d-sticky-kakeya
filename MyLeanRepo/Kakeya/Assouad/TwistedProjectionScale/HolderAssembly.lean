import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.HolderVolumeBound
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Hölder volume assembly for the twisted projection

Defines the twisted projection multiplicity (count of shaded tubes whose
projected image covers each point) and applies the Hölder volume lower bound
to obtain a volume lower bound on the twisted union.

Whiteprint node: `holder_assembly`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Coordinate access for `point3`. -/
private lemma point3_coord0 (x y z : ℝ) : (point3 x y z) 0 = x := by
  simp [point3]

private lemma point3_coord1 (x y z : ℝ) : (point3 x y z) 1 = y := by
  simp [point3]

private lemma point3_coord2 (x y z : ℝ) : (point3 x y z) 2 = z := by
  simp [point3]

/-- Reconstructing a Point2 from its coordinates is the identity. -/
private lemma point2_eta (p : Point2) :
    (p 0) • EuclideanSpace.single (0 : Fin 2) 1 +
      (p 1) • EuclideanSpace.single (1 : Fin 2) 1 = p := by
  ext i
  fin_cases i <;> simp

/--
Twisted projection multiplicity: number of shaded tubes whose twisted
projection image covers `p`.
-/
def twistedProjectionMultiplicity
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (p : Point2) : ENNReal :=
  ∑ i : Fin F.card,
    (twistedProjection f '' Z.carrier i).indicator (fun _ => (1 : ENNReal)) p

/-- The projected multiplicity is measurable when every projected carrier is. -/
lemma measurable_twistedProjectionMultiplicity_of_images
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (himage :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i)) :
    Measurable (twistedProjectionMultiplicity Z f) := by
  classical
  unfold twistedProjectionMultiplicity
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (himage i)

/-- The integral of projected multiplicity is the sum of projected areas. -/
lemma lintegral_twistedProjectionMultiplicity
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (himage :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i)) :
    ∫⁻ p, twistedProjectionMultiplicity Z f p =
      ∑ i : Fin F.card,
        volume (twistedProjection f '' Z.carrier i) := by
  classical
  unfold twistedProjectionMultiplicity
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.lintegral_indicator_const (himage i)]
    simp
  · intro i _
    exact measurable_const.indicator (himage i)

/--
Sum one-tube projection-area lower bounds into the total mass lower bound
required by Hölder.
-/
lemma mass_div_le_lintegral_twistedProjectionMultiplicity
    {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (himage :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i))
    (harea :
      ∀ i,
        volume (Z.carrier i) ≤
          ENNReal.ofReal (20 * δ) *
            volume (twistedProjection f '' Z.carrier i)) :
    Z.mass / ENNReal.ofReal (20 * δ) ≤
      ∫⁻ p, twistedProjectionMultiplicity Z f p := by
  have hc_pos : 0 < ENNReal.ofReal (20 * δ) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hc_ne : ENNReal.ofReal (20 * δ) ≠ 0 := hc_pos.ne'
  have hc_top : ENNReal.ofReal (20 * δ) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hsum :
      Z.mass ≤
        ENNReal.ofReal (20 * δ) *
          ∑ i : Fin F.card,
            volume (twistedProjection f '' Z.carrier i) := by
    calc
      Z.mass
          = ∑ i : Fin F.card, volume (Z.carrier i) := rfl
      _ ≤ ∑ i : Fin F.card,
            ENNReal.ofReal (20 * δ) *
              volume (twistedProjection f '' Z.carrier i) :=
          Finset.sum_le_sum fun i _ => harea i
      _ = ENNReal.ofReal (20 * δ) *
            ∑ i : Fin F.card,
              volume (twistedProjection f '' Z.carrier i) := by
          rw [Finset.mul_sum]
  have hdiv :
      Z.mass / ENNReal.ofReal (20 * δ) ≤
        ∑ i : Fin F.card,
          volume (twistedProjection f '' Z.carrier i) := by
    exact (ENNReal.div_le_iff' hc_ne hc_top).2 hsum
  calc
    Z.mass / ENNReal.ofReal (20 * δ)
        ≤ ∑ i : Fin F.card,
            volume (twistedProjection f '' Z.carrier i) := hdiv
    _ = ∫⁻ p, twistedProjectionMultiplicity Z f p :=
      (lintegral_twistedProjectionMultiplicity Z f himage).symm

/-- The support is exactly the twisted union. -/
lemma support_twistedProjectionMultiplicity
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) :
    {p | twistedProjectionMultiplicity Z f p ≠ 0} = twistedUnion Z f := by
  ext p
  simp only [Set.mem_setOf_eq, twistedProjectionMultiplicity]
  have h : (∑ i : Fin F.card,
      (twistedProjection f '' Z.carrier i).indicator (fun _ => (1 : ENNReal)) p) ≠ 0 ↔
      ∃ i : Fin F.card, p ∈ twistedProjection f '' Z.carrier i := by
    have h1 : (∑ i : Fin F.card,
        (twistedProjection f '' Z.carrier i).indicator (fun _ => (1 : ENNReal)) p) ≠ 0 ↔
        ∃ i : Fin F.card,
          (twistedProjection f '' Z.carrier i).indicator (fun _ => (1 : ENNReal)) p ≠ 0 := by
      simp [Finset.sum_eq_zero_iff_of_nonneg]
      <;> tauto
    rw [h1]
    simp [Set.indicator_apply]
    <;> tauto
  rw [h]
  simp [twistedUnion, Kakeya.Streamlined.Shading.union]
  <;> tauto

/--
Hölder volume assembly for the twisted projection.

Given a measurable multiplicity function `m` on `Point2` with support contained
in the twisted union, total mass at least `S`, and L^{3/2} norm at most `M`,
the volume of the twisted union is at least `(S/M)^3`.
-/
lemma holder_twistedUnion_volume
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Z : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    {m : Point2 → ENNReal}
    (hm : Measurable m)
    (S M : ENNReal)
    (hS : S ≤ ∫⁻ p, m p)
    (hM : eLpNorm m (3 / 2 : ENNReal) volume ≤ M)
    (h_support : {p | m p ≠ 0} ⊆ twistedUnion Z f) :
    volume (twistedUnion Z f) ≥ (S / M) ^ 3 := by
  let U : Set Point2 := {p | m p ≠ 0}
  have hU_meas : MeasurableSet U := by
    have h1 : MeasurableSet ({0} : Set ENNReal) := measurableSet_singleton 0
    exact (hm h1).compl
  have h_main : volume U ≥ ((∫⁻ p, m p) / M) ^ 3 :=
    holder_volume_lower_bound hm (∫⁻ p, m p) M rfl hM
  have h_S_le : (S / M) ^ 3 ≤ ((∫⁻ p, m p) / M) ^ 3 := by
    gcongr
  have h_mono : volume U ≤ volume (twistedUnion Z f) :=
    measure_mono h_support
  exact h_S_le.trans (h_main.trans h_mono)

/--
Apply Hölder to compact projected carriers once the one-tube area estimates
and a projected-multiplicity norm bound are available.
-/
lemma holder_twistedUnion_volume_of_projected_areas
    {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Z : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (himage :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i))
    (harea :
      ∀ i,
        volume (Z.carrier i) ≤
          ENNReal.ofReal (20 * δ) *
            volume (twistedProjection f '' Z.carrier i))
    (M : ENNReal)
    (hM :
      eLpNorm (twistedProjectionMultiplicity Z f)
        (3 / 2 : ENNReal) volume ≤ M) :
    volume (twistedUnion Z f) ≥
      ((Z.mass / ENNReal.ofReal (20 * δ)) / M) ^ 3 := by
  apply holder_twistedUnion_volume
    (measurable_twistedProjectionMultiplicity_of_images Z f himage)
    (Z.mass / ENNReal.ofReal (20 * δ)) M
  · exact mass_div_le_lintegral_twistedProjectionMultiplicity
      hδ Z f himage harea
  · exact hM
  · rw [support_twistedProjectionMultiplicity Z f]

end Kakeya.Assouad
