import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPartition
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-!
# Property-(P) selection by multiplicity energy

For every tube, fill all grid cells touched by its actual shading and measure
the total shaded incidence mass in that region.  Finite Fubini and the `L²`
multiplicity energy select one genuine tube whose region is quantitatively
popular.  Restricting all shadings to that region gives the literal
same-grid-cell Property (P).

The result deliberately records the exact energy inequality.  It does not
claim a constant retained fraction; such a claim is false without additional
structure.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The union of all `scale`-grid cells touched by one shaded tube. -/
def propertyPOccupiedRegion
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (index : Fin family.card) : Set Point3 :=
  {point | ∃ witness ∈ shading.carrier index,
    rhoGridIndex scale point = rhoGridIndex scale witness}

lemma propertyPOccupiedRegion_measurable
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (index : Fin family.card) :
    MeasurableSet (propertyPOccupiedRegion scale shading index) := by
  let grid : Point3 → ℤ × ℤ × ℤ := rhoGridIndex scale
  have hgrid : Measurable grid := by
    have hfloor : Measurable (Int.floor : ℝ → ℤ) :=
      Int.measurable_floor
    have h0 : Measurable (fun point : Point3 =>
        ⌊point 0 / gridSide scale⌋) :=
      hfloor.comp (by fun_prop)
    have h1 : Measurable (fun point : Point3 =>
        ⌊point 1 / gridSide scale⌋) :=
      hfloor.comp (by fun_prop)
    have h2 : Measurable (fun point : Point3 =>
        ⌊point 2 / gridSide scale⌋) :=
      hfloor.comp (by fun_prop)
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / gridSide scale⌋,
          ⌊point 1 / gridSide scale⌋,
          ⌊point 2 / gridSide scale⌋)) :=
      h0.prod (h1.prod h2)
    convert h using 1
    funext point
    simp [grid, rhoGridIndex, gridIndex]
  let touched : Set (ℤ × ℤ × ℤ) := grid '' shading.carrier index
  have htouched : MeasurableSet touched := MeasurableSet.of_discrete
  have heq : propertyPOccupiedRegion scale shading index =
      grid ⁻¹' touched := by
    ext point
    constructor
    · rintro ⟨witness, hwitness, hgridEq⟩
      exact ⟨witness, hwitness, hgridEq.symm⟩
    · rintro ⟨witness, hwitness, hgridEq⟩
      exact ⟨witness, hwitness, hgridEq.symm⟩
  rw [heq]
  exact hgrid htouched

lemma carrier_subset_propertyPOccupiedRegion
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (index : Fin family.card) :
    shading.carrier index ⊆
      propertyPOccupiedRegion scale shading index := by
  intro point hpoint
  exact ⟨point, hpoint, rfl⟩

/-- Total shaded incidence mass inside one tube's occupied grid region. -/
def propertyPCapturedMass
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (index : Fin family.card) : ENNReal :=
  ∑ other : Fin family.card,
    volume (shading.carrier other ∩
      propertyPOccupiedRegion scale shading index)

/-- Restrict every tube to the grid cells touched by `distinguished`. -/
def propertyPEnergyRefinement
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (distinguished : Fin family.card) :
    Kakeya.Streamlined.Shading family where
  carrier index := shading.carrier index ∩
    propertyPOccupiedRegion scale shading distinguished
  measurable_carrier index :=
    (shading.measurable_carrier index).inter
      (propertyPOccupiedRegion_measurable scale shading distinguished)
  subset_body index :=
    Set.inter_subset_left.trans (shading.subset_body index)

@[simp] lemma propertyPEnergyRefinement_carrier
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (distinguished index : Fin family.card) :
    (propertyPEnergyRefinement scale shading distinguished).carrier index =
      shading.carrier index ∩
        propertyPOccupiedRegion scale shading distinguished := rfl

lemma propertyPEnergyRefinement_subshading
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (distinguished : Fin family.card) :
    ∀ index,
      (propertyPEnergyRefinement scale shading distinguished).carrier index ⊆
        shading.carrier index :=
  fun _ => Set.inter_subset_left

lemma propertyPEnergyRefinement_mass
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (distinguished : Fin family.card) :
    (propertyPEnergyRefinement scale shading distinguished).mass =
      propertyPCapturedMass scale shading distinguished := rfl

lemma propertyPEnergyRefinement_propertyP
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (distinguished : Fin family.card) :
    ∀ point ∈
        (propertyPEnergyRefinement scale shading distinguished).union,
      ∃ witness ∈
          (propertyPEnergyRefinement scale shading distinguished).carrier
            distinguished,
        rhoGridIndex scale point = rhoGridIndex scale witness := by
  intro point hpoint
  rcases hpoint with ⟨index, hcarrier, hregion⟩
  rcases hregion with ⟨witness, hwitness, hcell⟩
  refine ⟨witness, ⟨hwitness, ?_⟩, hcell⟩
  exact ⟨witness, hwitness, rfl⟩

private lemma pointMultiplicity_lintegral_square
    {family : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading family) :
    (∫⁻ point, ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ))) =
      ∑ first : Fin family.card, ∑ second : Fin family.card,
        volume (shading.carrier first ∩ shading.carrier second) := by
  have hsquare : ∀ point,
      ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ)) =
        ∑ first : Fin family.card, ∑ second : Fin family.card,
          (shading.carrier first ∩ shading.carrier second).indicator
            (fun _ => (1 : ENNReal)) point := by
    intro point
    rw [ENNReal.rpow_two]
    have hindicator :
        (shading.pointMultiplicity point : ENNReal) =
          ∑ index : Fin family.card,
            (shading.carrier index).indicator
              (fun _ => (1 : ENNReal)) point := by
      exact coe_pointMultiplicity_eq_sum_indicator shading point
    rw [hindicator, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    by_cases hfirst : point ∈ shading.carrier first <;>
      by_cases hsecond : point ∈ shading.carrier second <;>
      simp [hfirst, hsecond]
  rw [MeasureTheory.lintegral_congr hsquare]
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro first _
    rw [MeasureTheory.lintegral_finset_sum]
    · apply Finset.sum_congr rfl
      intro second _
      exact MeasureTheory.lintegral_indicator_one
        ((shading.measurable_carrier first).inter
          (shading.measurable_carrier second))
    · intro second _
      exact measurable_const.indicator
        ((shading.measurable_carrier first).inter
          (shading.measurable_carrier second))
  · intro first _
    exact Finset.measurable_sum Finset.univ (by
      intro second _
      exact measurable_const.indicator
        ((shading.measurable_carrier first).inter
          (shading.measurable_carrier second)))

private lemma pointMultiplicity_cauchy_schwarz
    {family : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading family) :
    shading.mass ^ 2 ≤ volume shading.union *
      (∫⁻ point, ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ))) := by
  let multiplicity : Point3 → ENNReal := fun point =>
    (shading.pointMultiplicity point : ENNReal)
  let support : Point3 → ENNReal :=
    shading.union.indicator (fun _ => (1 : ENNReal))
  have hmultiplicity : Measurable multiplicity := by
    exact (measurable_of_countable fun n : ℕ => (n : ENNReal)).comp
      (measurable_pointMultiplicity shading)
  have hunion : MeasurableSet shading.union :=
    measurableSet_shading_union shading
  have hsupport : Measurable support :=
    measurable_const.indicator hunion
  have hmul : ∀ point, multiplicity point * support point =
      multiplicity point := by
    intro point
    by_cases hpoint : point ∈ shading.union
    · simp [support, hpoint]
    · have hzero : shading.pointMultiplicity point = 0 := by
        apply Finset.card_eq_zero.mpr
        simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
        intro index hcarrier
        exact hpoint ⟨index, hcarrier⟩
      simp [support, multiplicity, hpoint, hzero]
  have hmass : (∫⁻ point, multiplicity point * support point) =
      shading.mass := by
    rw [MeasureTheory.lintegral_congr hmul]
    exact lintegral_pointMultiplicity shading
  have hsupportSquare : ∀ point, support point ^ (2 : ℝ) =
      support point := by
    intro point
    by_cases hpoint : point ∈ shading.union <;>
      simp [support, hpoint]
  have hsupportIntegral :
      (∫⁻ point, support point ^ (2 : ℝ)) = volume shading.union := by
    rw [MeasureTheory.lintegral_congr hsupportSquare]
    exact MeasureTheory.lintegral_indicator_one hunion
  have hholder :
      (∫⁻ point, multiplicity point * support point) ≤
        (∫⁻ point, multiplicity point ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ point, support point ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      Real.HolderConjugate.two_two
      hmultiplicity.aemeasurable hsupport.aemeasurable
  rw [hmass, hsupportIntegral] at hholder
  have hsquare := pow_le_pow_left₀ (by simp) hholder 2
  have hpow : ∀ value : ENNReal,
      (value ^ (1 / 2 : ℝ)) ^ 2 = value := by
    intro value
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    shading.mass ^ 2
        ≤ (((∫⁻ point, multiplicity point ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) *
            (volume shading.union ^ (1 / 2 : ℝ))) ^ 2 := hsquare
    _ = (∫⁻ point, multiplicity point ^ (2 : ℝ)) *
          volume shading.union := by
        rw [mul_pow, hpow, hpow]
    _ = volume shading.union *
          (∫⁻ point,
            ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ))) := by
        rw [mul_comm]

private lemma multiplicity_energy_le_captured_sum
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family) :
    (∫⁻ point, ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ))) ≤
      ∑ index : Fin family.card,
        propertyPCapturedMass scale shading index := by
  rw [pointMultiplicity_lintegral_square shading]
  apply Finset.sum_le_sum
  intro first _
  apply Finset.sum_le_sum
  intro second _
  exact measure_mono (by
    intro point hpoint
    exact ⟨hpoint.2,
      carrier_subset_propertyPOccupiedRegion scale shading first hpoint.1⟩)

/--
Select a genuine distinguished tube by multiplicity energy.  The returned
refinement has literal Property (P), and its mass satisfies the exact
energy lower bound used for later loss accounting.
-/
theorem property_p_energy_selection
    {family : Kakeya.Streamlined.BodyFamily}
    (scale : ℝ) (shading : Kakeya.Streamlined.Shading family)
    (hfamily : 0 < family.card) :
    ∃ (distinguished : Fin family.card)
      (selected : Kakeya.Streamlined.Shading family),
      (∀ index, selected.carrier index ⊆ shading.carrier index) ∧
      (∀ index, selected.carrier index =
        shading.carrier index ∩
          propertyPOccupiedRegion scale shading distinguished) ∧
      (∀ point ∈ selected.union,
        ∃ witness ∈ selected.carrier distinguished,
          rhoGridIndex scale point = rhoGridIndex scale witness) ∧
      shading.mass ^ 2 ≤
        volume shading.union * (family.card : ENNReal) * selected.mass := by
  have huniv : (Finset.univ : Finset (Fin family.card)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr ⟨0, hfamily⟩
  obtain ⟨distinguished, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin family.card))
      (propertyPCapturedMass scale shading) huniv
  let selected := propertyPEnergyRefinement scale shading distinguished
  have hsum :
      (∑ index : Fin family.card,
          propertyPCapturedMass scale shading index) ≤
        (family.card : ENNReal) *
          propertyPCapturedMass scale shading distinguished := by
    calc
      (∑ index : Fin family.card,
          propertyPCapturedMass scale shading index)
          ≤ ∑ _index : Fin family.card,
              propertyPCapturedMass scale shading distinguished := by
            apply Finset.sum_le_sum
            intro index _
            exact hmax index (Finset.mem_univ index)
      _ = (family.card : ENNReal) *
            propertyPCapturedMass scale shading distinguished := by
          simp [Finset.sum_const]
  refine ⟨distinguished, selected,
    propertyPEnergyRefinement_subshading scale shading distinguished,
    (fun _ => rfl),
    propertyPEnergyRefinement_propertyP scale shading distinguished, ?_⟩
  calc
    shading.mass ^ 2 ≤ volume shading.union *
        (∫⁻ point, ((shading.pointMultiplicity point : ENNReal) ^ (2 : ℝ))) :=
      pointMultiplicity_cauchy_schwarz shading
    _ ≤ volume shading.union *
        (∑ index : Fin family.card,
          propertyPCapturedMass scale shading index) := by
      gcongr
      exact multiplicity_energy_le_captured_sum scale shading
    _ ≤ volume shading.union *
        ((family.card : ENNReal) *
          propertyPCapturedMass scale shading distinguished) := by gcongr
    _ = volume shading.union * (family.card : ENNReal) * selected.mass := by
      rw [propertyPEnergyRefinement_mass]
      ring

end Kakeya.Assouad

end
