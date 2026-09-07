import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperDirectionPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperDirectionPackingGeneral
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaProjectionCoveringGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.MultiScaleAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLower

/-!
# Local AD bounds for Pure WZ2 grains

Establishes the every-scale local Assouad-dimension bound on the scalar projection
of the shaded union near each point, following WZ1 Lemmas 17–20 adapted to the
Pure WZ2 balanced-cover setting.

## Proof structure

The 1-σ exponent requires the Córdoba L² slab lower bound, which in turn needs a
property-(P) refinement: a subshading with constant multiplicity, local fullness,
and a transverse direction at every point.

### Geometric core (UTS-free, reused from WZ1)

1. **Direction packing** (`wz1_coarse_direction_packing`): essentially distinct
   tubes have universally bounded close-direction count at any point.
2. **Grid cell pruning** (`gridCellPrune`): retains points with enough local mass.
3. **Multiplicity extraction** (`extract_constant_multiplicity`): selects a
   constant-multiplicity subshading.
4. **Transverse selection** (`transverse_from_close_count_lt_multiplicity`):
   given close-direction count below multiplicity, picks a transverse tube.
5. **Córdoba covering lemma** (`covering_number_from_slab_volumes_subset`):
   converts slab volume bounds to covering-number bounds.

### PureWZ2-specific adaptation

The WZ1 refinement references `UniformTubeStructure` for the coarse family,
multi-scale balanced covers, and `WZ1ExtremalPair`. We replace these with:
- `sticky.coarse` family (from PropStickyData)
- Single balanced cover at scale L = rho.1
- `WZ2PaperCroppedIsExtremal` for volume upper and density
- `coarse_multiplicity_upper` and `fiber_multiplicity_upper`

## Remaining proof obligations

The property-(P) construction and Córdoba L² bound are the critical path.
See `PureWZ2PropertyPData` for the exact output specification.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-!
## Paper-shading compatibility helpers
-/

/--
Grid-cell prune a paper tube shading.

Retains only grid cells at scale `tau/2` where the carrier has at least
`threshold` volume.  This guarantees local fullness: every retained point
has at least `threshold` volume in its radius-`tau` ball.
-/
def paperGridCellPrune
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F)
    (tau threshold : ℝ) (htau : 0 < tau) :
    WZ1PaperTubeShading F :=
  let good (index : Fin F.card) (cell : ℤ × ℤ × ℤ) : Prop :=
    ENNReal.ofReal threshold ≤
      volume (Y.carrier index ∩ gridCell tau cell)
  { carrier := fun index =>
      {point |
        ∃ cell : ℤ × ℤ × ℤ,
          good index cell ∧
            point ∈ Y.carrier index ∩ gridCell tau cell}
    measurable_carrier := by
      intro index
      have heq :
          {point : Point3 |
              ∃ cell : ℤ × ℤ × ℤ,
                good index cell ∧
                  point ∈ Y.carrier index ∩ gridCell tau cell} =
          ⋃ cell : ℤ × ℤ × ℤ,
            if good index cell then
              Y.carrier index ∩ gridCell tau cell
            else ∅ := by
        ext point
        simp [good]
      rw [heq]
      apply MeasurableSet.iUnion
      intro cell
      by_cases hgood : good index cell
      · rw [if_pos hgood]
        exact (Y.measurable_carrier index).inter (gridCell_measurable cell)
      · rw [if_neg hgood]
        exact MeasurableSet.empty
    subset_body := by
      intro index point hpoint
      rcases hpoint with ⟨cell, _, hpointCarrier, _⟩
      exact Y.subset_body index hpointCarrier }

/-- Paper grid-cell pruning is a subshading. -/
lemma paperGridCellPrune_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {tau threshold : ℝ} {htau : 0 < tau} :
    PaperIsSubshading (paperGridCellPrune Y tau threshold htau) Y := by
  intro index point hpoint
  rcases hpoint with ⟨cell, _, hpointCarrier, _⟩
  exact hpointCarrier

/-- Every retained point has the prescribed mass in its radius-`tau` ball. -/
lemma paperGridCellPrune_fullness
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {tau threshold : ℝ} (htau : 0 < tau)
    (_hthreshold : 0 ≤ threshold)
    {index : Fin F.card} {point : Point3}
    (hpoint : point ∈ (paperGridCellPrune Y tau threshold htau).carrier index) :
    ENNReal.ofReal threshold ≤
      volume ((paperGridCellPrune Y tau threshold htau).carrier index ∩
        Metric.closedBall point tau) := by
  rcases hpoint with ⟨cell, hgood, hpointCarrier, hpointCell⟩
  have heq :
      (paperGridCellPrune Y tau threshold htau).carrier index ∩ gridCell tau cell =
        Y.carrier index ∩ gridCell tau cell := by
    ext other
    constructor
    · rintro ⟨⟨_, _, hotherCarrier, _⟩, hotherCell⟩
      exact ⟨hotherCarrier, hotherCell⟩
    · rintro ⟨hotherCarrier, hotherCell⟩
      exact ⟨⟨cell, hgood, hotherCarrier, hotherCell⟩, hotherCell⟩
  have h1 : ENNReal.ofReal threshold ≤
      volume ((paperGridCellPrune Y tau threshold htau).carrier index ∩ gridCell tau cell) := by
    rw [heq]
    exact hgood
  exact h1.trans (measure_mono fun x hx =>
    ⟨hx.1, gridCell_diameter htau hx.2 hpointCell⟩)

/-!
## Paper-shading multiplicity extraction

Adapts the two-level constant-multiplicity extraction to paper tube shadings.
-/

/-- Restrict a paper shading to points in a measurable set. -/
def paperRestrictShadingToSet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Z : WZ1PaperTubeShading F) (S : Set Point3)
    (hS : MeasurableSet S) : WZ1PaperTubeShading F :=
  { carrier := fun j => Z.carrier j ∩ S
    measurable_carrier := fun j => (Z.measurable_carrier j).inter hS
    subset_body := fun j _ hx => Z.subset_body j hx.1 }

/-- Mass of a paper shading restricted to a measurable set. -/
lemma paperMassRestrictShadingToSet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : WZ1PaperTubeShading F} {S : Set Point3}
    (hS : MeasurableSet S) :
    (paperRestrictShadingToSet Z S hS).mass =
      ∫⁻ p in S, (Z.pointMultiplicity p : ENNReal) := by
  have h1 : (paperRestrictShadingToSet Z S hS).mass =
      ∑ i, volume (Z.carrier i ∩ S) := by rfl
  rw [h1]
  exact sum_volume_inter_eq_setLIntegral_pointMultiplicity Z hS

/-- Point multiplicity equality on the restricting set. -/
lemma paperPmRestrictShadingToSet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z : WZ1PaperTubeShading F} {S : Set Point3}
    (hS : MeasurableSet S) {p : Point3} (hp : p ∈ S) :
    (paperRestrictShadingToSet Z S hS).pointMultiplicity p =
      Z.pointMultiplicity p := by
  have h_iff : ∀ (k : Fin F.card),
      p ∈ (paperRestrictShadingToSet Z S hS).carrier k ↔ p ∈ Z.carrier k := by
    intro k
    simp only [paperRestrictShadingToSet, Set.mem_inter_iff]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, hp⟩
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr
  ext k
  exact h_iff k

/-- Points of a paper shading with multiplicity at least `threshold`. -/
def paperHighMultiplicitySet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (threshold : ENNReal) : Set Point3 :=
  {p ∈ Y.union | threshold ≤ (Y.pointMultiplicity p : ENNReal)}

lemma measurableSet_paperHighMultiplicitySet
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading F) (threshold : ENNReal) :
    MeasurableSet (paperHighMultiplicitySet Y threshold) := by
  have h1 : MeasurableSet Y.union := measurableSet_shading_union Y
  have h_meas : Measurable (fun p : Point3 => (Y.pointMultiplicity p : ENNReal)) := by
    have h1 : Measurable (Y.pointMultiplicity) := measurable_pointMultiplicity Y
    have h2 : Measurable (fun n : ℕ => (n : ENNReal)) := measurable_of_countable _
    exact h2.comp h1
  have h2 : MeasurableSet {p : Point3 | threshold ≤ (Y.pointMultiplicity p : ENNReal)} := by
    exact measurableSet_le measurable_const h_meas
  exact h1.inter h2

/-- If the low-multiplicity contribution is below half the total mass, the
explicit high-multiplicity restriction retains at least half the mass. -/
lemma paperHighMultiplicityRestriction_half_mass
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {threshold : ENNReal}
    (hY_mass_ne_top : Y.mass ≠ ⊤)
    (h_avg : threshold * volume Y.union <
      (1 / 2 : ENNReal) * Y.mass) :
    (1 / 2 : ENNReal) * Y.mass ≤
      (paperRestrictShadingToSet Y
        (paperHighMultiplicitySet Y threshold)
        (measurableSet_paperHighMultiplicitySet Y threshold)).mass := by
  let high : Set Point3 := paperHighMultiplicitySet Y threshold
  let low : Set Point3 := Y.union \ high
  let mult : Point3 → ENNReal := fun p => (Y.pointMultiplicity p : ENNReal)
  have hhigh_meas : MeasurableSet high :=
    measurableSet_paperHighMultiplicitySet Y threshold
  have hlow_meas : MeasurableSet low :=
    (measurableSet_shading_union Y).diff hhigh_meas
  have hlow_point : ∀ p ∈ low, mult p ≤ threshold := by
    intro p hp
    have hp_union : p ∈ Y.union := hp.1
    have hp_not : p ∉ high := hp.2
    have hnot : ¬ threshold ≤ mult p := by
      intro hle
      exact hp_not ⟨hp_union, hle⟩
    exact le_of_not_ge hnot
  have hlow_mass :
      (∫⁻ p in low, mult p) ≤ threshold * volume low := by
    calc
      (∫⁻ p in low, mult p) ≤ ∫⁻ _p in low, threshold := by
        apply MeasureTheory.setLIntegral_mono' hlow_meas
        intro p hp
        exact hlow_point p hp
      _ = threshold * volume low := by
        rw [MeasureTheory.setLIntegral_const]
  have hlow_half :
      (∫⁻ p in low, mult p) ≤ (1 / 2 : ENNReal) * Y.mass := by
    calc
      (∫⁻ p in low, mult p) ≤ threshold * volume low := hlow_mass
      _ ≤ threshold * volume Y.union := by
        exact mul_le_mul_left'
          (measure_mono (μ := volume)
            (show low ⊆ Y.union from Set.diff_subset)) threshold
      _ ≤ (1 / 2 : ENNReal) * Y.mass := h_avg.le
  have hdisj : Disjoint high low := by
    rw [Set.disjoint_left]
    intro p hp_high hp_low
    exact hp_low.2 hp_high
  have hunion : high ∪ low = Y.union := by
    ext p
    constructor
    · intro hp
      rcases hp with hp | hp
      · exact hp.1
      · exact hp.1
    · intro hp
      by_cases hph : p ∈ high
      · exact Or.inl hph
      · exact Or.inr ⟨hp, hph⟩
  have htotal : Y.mass = ∫⁻ p in Y.union, mult p := by
    have hsum := sum_volume_inter_eq_setLIntegral_pointMultiplicity
      Y (measurableSet_shading_union Y)
    have hinter : ∀ i, Y.carrier i ∩ Y.union = Y.carrier i := by
      intro i
      apply Set.inter_eq_left.mpr
      intro p hp
      exact ⟨i, hp⟩
    have hleft :
        (∑ i, volume (Y.carrier i ∩ Y.union)) = Y.mass := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hinter i]
    exact hleft.symm.trans hsum
  have hsplit :
      Y.mass = (∫⁻ p in high, mult p) + (∫⁻ p in low, mult p) := by
    calc
      Y.mass = ∫⁻ p in Y.union, mult p := htotal
      _ = ∫⁻ p in (high ∪ low), mult p := by rw [hunion]
      _ = (∫⁻ p in high, mult p) + (∫⁻ p in low, mult p) :=
        lintegral_union hlow_meas hdisj
  have hhigh_mass :
      (paperRestrictShadingToSet Y high hhigh_meas).mass =
        ∫⁻ p in high, mult p := by
    exact paperMassRestrictShadingToSet hhigh_meas
  let halfMass : ENNReal := (1 / 2 : ENNReal) * Y.mass
  have hbound : Y.mass ≤
      (paperRestrictShadingToSet Y high hhigh_meas).mass + halfMass := by
    rw [hsplit, hhigh_mass]
    simpa [halfMass, add_comm] using
      add_le_add_right hlow_half (∫⁻ p in high, mult p)
  have hhalf_add : halfMass + halfMass = Y.mass := by
    dsimp only [halfMass]
    have hhalf : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
      have hdiv : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [hdiv, ← two_mul]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
    rw [← add_mul, hhalf, one_mul]
  have hhalf_top : halfMass ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hY_mass_ne_top
  have hcancel :
      halfMass + halfMass ≤
        (paperRestrictShadingToSet Y high hhigh_meas).mass + halfMass := by
    rw [hhalf_add]
    exact hbound
  have hresult : halfMass ≤
      (paperRestrictShadingToSet Y high hhigh_meas).mass :=
    (ENNReal.add_le_add_iff_right hhalf_top).mp hcancel
  simpa [halfMass, high] using hresult

/-- The high-multiplicity set of a cubical shading is a union of paper cells. -/
lemma paperHighMultiplicitySet_cube_union
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {threshold : ENNReal}
    (hcubical : WZ1PaperIsCubicalShading Y) :
    ∀ p ∈ paperHighMultiplicitySet Y threshold,
      wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆
        paperHighMultiplicitySet Y threshold := by
  intro p hp q hq
  have hindex : wz1PaperGridIndex delta q =
      wz1PaperGridIndex delta p :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta p) q).mp hq
  have hcarrier : ∀ i : Fin F.card,
      p ∈ Y.carrier i ↔ q ∈ Y.carrier i := by
    intro i
    constructor
    · intro hpCarrier
      exact hcubical i p hpCarrier hq
    · intro hqCarrier
      have hcube := hcubical i q hqCarrier
      have hpCell : p ∈
          wz1PaperGridCube delta (wz1PaperGridIndex delta q) := by
        rw [mem_wz1PaperGridCube]
        exact hindex.symm
      exact hcube hpCell
  have hmultiplicity : Y.pointMultiplicity q = Y.pointMultiplicity p := by
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    ext i
    simpa using (hcarrier i).symm
  have hqunion : q ∈ Y.union := by
    rcases hp.1 with ⟨i, hi⟩
    exact ⟨i, (hcarrier i).mp hi⟩
  exact ⟨hqunion, by rw [hmultiplicity]; exact hp.2⟩

/-- Restricting a cubical shading to a union of paper cells preserves
cubicality. -/
lemma paperRestrictShadingToSet_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {S : Set Point3}
    (hS : MeasurableSet S)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (hwhole : ∀ p ∈ S,
      wz1PaperGridCube delta (wz1PaperGridIndex delta p) ⊆ S) :
    WZ1PaperIsCubicalShading (paperRestrictShadingToSet Y S hS) := by
  intro i p hp q hq
  exact ⟨hcubical i p hp.1 hq, hwhole p hp.2 hq⟩

/-- In particular, a high-multiplicity restriction of a cubical shading is
cubical. -/
lemma paperHighMultiplicityRestriction_cubical
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {threshold : ENNReal}
    (hcubical : WZ1PaperIsCubicalShading Y) :
    WZ1PaperIsCubicalShading
      (paperRestrictShadingToSet Y
        (paperHighMultiplicitySet Y threshold)
        (measurableSet_paperHighMultiplicitySet Y threshold)) :=
  paperRestrictShadingToSet_cubical
    (measurableSet_paperHighMultiplicitySet Y threshold) hcubical
    (paperHighMultiplicitySet_cube_union hcubical)

/-- If `threshold * volume(union) < mass`, the high-multiplicity set is nonempty. -/
lemma paperHighMultiplicitySet_nonempty
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {threshold : ENNReal}
    (hY_mass_ne_top : Y.mass ≠ ⊤)
    (h_volume_ne_top : volume Y.union ≠ ⊤)
    (h_avg : threshold * volume Y.union < Y.mass) :
    (paperHighMultiplicitySet Y threshold).Nonempty := by
  let S := paperHighMultiplicitySet Y threshold
  let T := Y.union \ S
  have hS_meas : MeasurableSet S := measurableSet_paperHighMultiplicitySet Y threshold
  have hT_meas : MeasurableSet T :=
    (measurableSet_shading_union Y).diff hS_meas
  by_cases hS_empty : S = ∅
  · -- Assume S is empty, derive contradiction
    have hT_eq : T = Y.union := by
      dsimp only [T]
      rw [hS_empty]
      <;> simp
    have h_mult_lt : ∀ p ∈ T, (Y.pointMultiplicity p : ENNReal) < threshold := by
      intro p hp
      have h_p_in_union : p ∈ Y.union := by
        rw [hT_eq] at hp <;> exact hp
      have h_not_in_S : p ∉ S := by
        rw [hS_empty] <;> simp
      have h_iff : p ∈ S ↔ threshold ≤ (Y.pointMultiplicity p : ENNReal) := by
        have h : p ∈ S ↔ p ∈ Y.union ∧ threshold ≤ (Y.pointMultiplicity p : ENNReal) := by
          rfl
        rw [h]
        exact ⟨fun h' => h'.2, fun h' => ⟨h_p_in_union, h'⟩⟩
      have h : ¬(threshold ≤ (Y.pointMultiplicity p : ENNReal)) := by
        exact h_iff.not.mp h_not_in_S
      exact lt_of_not_ge h
    have h_mass_T : ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) ≤ threshold * volume T := by
      calc
        (∫⁻ p in T, (Y.pointMultiplicity p : ENNReal))
          ≤ ∫⁻ p in T, threshold := by
            apply MeasureTheory.setLIntegral_mono' hT_meas
            intro p hp
            exact (h_mult_lt p hp).le
        _ = threshold * volume T := by
          rw [MeasureTheory.setLIntegral_const]
    have h_mass_eq : Y.mass = ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) := by
      have h1 : Y.mass = ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) := by
        have h_sum : ∑ i : Fin F.card, volume (Y.carrier i ∩ Y.union) =
            ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) :=
          sum_volume_inter_eq_setLIntegral_pointMultiplicity Y (measurableSet_shading_union Y)
        have h2 : ∀ i, Y.carrier i ∩ Y.union = Y.carrier i := by
          intro i
          apply Set.inter_eq_left.mpr
          intro x hx
          exact ⟨i, hx⟩
        have h3 : ∑ i : Fin F.card, volume (Y.carrier i ∩ Y.union) = Y.mass := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h2 i]
        exact h3.symm.trans h_sum
      rw [h1, hT_eq]
    rw [h_mass_eq] at h_avg
    have h4 : ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) ≤ threshold * volume Y.union := by
      have h5 : volume T = volume Y.union := by rw [hT_eq]
      rw [h5] at h_mass_T
      exact h_mass_T
    have h5 : threshold * volume Y.union ≤ ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) :=
      le_of_lt h_avg
    have h6 : ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) ≤ threshold * volume Y.union := h4
    have h7 : threshold * volume Y.union = ∫⁻ p in T, (Y.pointMultiplicity p : ENNReal) :=
      le_antisymm h5 h6
    rw [h7] at h_avg
    simpa using h_avg
  · -- S is nonempty
    exact Set.nonempty_iff_ne_empty.mpr hS_empty

/--
Extract a constant-multiplicity subshading from a paper shading.

Given `Z ⊆ Y` with `Y` having constant multiplicity `[m, 2m]` and
`D := Y.mass - Z.mass ≤ Y.mass / 10`, there exists a subshading `W` of `Z`
with constant multiplicity `[a, 2a]`, `a ≥ (m+1)/2`, and mass at least
`Y.mass / 4`.
-/
lemma paperExtractConstantMultiplicity
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    {m : ℕ}
    (hsub : PaperIsSubshading Z Y)
    (hY_const : Y.HasConstantMultiplicity m (2 * m))
    (hZ_cubical : WZ1PaperIsCubicalShading Z)
    (hY_mass_ne_top : Y.mass ≠ ⊤)
    (hm_pos : 0 < m)
    (hD_small : Y.mass - Z.mass ≤ (1 / 10 : ENNReal) * Y.mass) :
    ∃ (a : ℕ) (W : WZ1PaperTubeShading F),
        PaperIsSubshading W Z ∧
        W.HasConstantMultiplicity a (2 * a) ∧
        a ≥ (m + 1) / 2 ∧
        (1 / 4 : ENNReal) * Y.mass ≤ W.mass ∧
        WZ1PaperIsCubicalShading W := by
  classical
  let D := Y.mass - Z.mass
  let d : Point3 → ℕ := fun p =>
    Y.pointMultiplicity p - Z.pointMultiplicity p
  let d_enn : Point3 → ENNReal := fun p =>
    (Y.pointMultiplicity p : ENNReal) - (Z.pointMultiplicity p : ENNReal)

  let B : Set Point3 := {p | 2 * Z.pointMultiplicity p < m}
  let S0 : Set Point3 :=
    {p | m ≤ 2 * Z.pointMultiplicity p ∧ Z.pointMultiplicity p < m}
  let S1 : Set Point3 := {p | m ≤ Z.pointMultiplicity p}

  have hZ_mass_le_Y : Z.mass ≤ Y.mass := by
    dsimp only [Kakeya.Streamlined.Shading.mass]
    apply Finset.sum_le_sum
    intro i _
    exact measure_mono (hsub i)
  have hZ_mass_ne_top : Z.mass ≠ ⊤ :=
    ne_top_of_le_ne_top hY_mass_ne_top hZ_mass_le_Y
  have hD_ne_top : D ≠ ⊤ := ne_top_of_le_ne_top hY_mass_ne_top tsub_le_self

  have hZ_meas : Measurable (Z.pointMultiplicity) := measurable_pointMultiplicity Z
  have hB_meas : MeasurableSet B := by
    have h2 : MeasurableSet ({n : ℕ | 2 * n < m} : Set ℕ) :=
      MeasurableSet.of_discrete
    exact hZ_meas h2
  have hS0_meas : MeasurableSet S0 := by
    have h2 : MeasurableSet ({n : ℕ | m ≤ 2 * n ∧ n < m} : Set ℕ) :=
      MeasurableSet.of_discrete
    exact hZ_meas h2
  have hS1_meas : MeasurableSet S1 := by
    exact hZ_meas (measurableSet_Ici)

  have h_ge : ∀ p, Z.pointMultiplicity p ≤ Y.pointMultiplicity p := by
    intro p
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hsub i hi

  have hZ_multiplicity_same_cell : ∀ {p q : Point3},
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        Z.pointMultiplicity p = Z.pointMultiplicity q := by
    intro p q hsame
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    constructor
    · intro hp
      exact hZ_cubical index p hp <|
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta p) q).mpr hsame.symm
    · intro hq
      exact hZ_cubical index q hq <|
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta q) p).mpr hsame

  have h_pointwise_add :
      ∀ p, Y.pointMultiplicity p = Z.pointMultiplicity p + d p := by
    intro p
    exact (Nat.add_sub_of_le (h_ge p)).symm

  have h_ennreal_add : ∀ p, (Y.pointMultiplicity p : ENNReal) =
      (Z.pointMultiplicity p : ENNReal) + (d p : ENNReal) := by
    intro p
    norm_cast
    exact h_pointwise_add p

  have h_d_enn_eq_d : ∀ p, d_enn p = (d p : ENNReal) := by
    intro p
    have h_eq1 : (Y.pointMultiplicity p : ENNReal) =
        (Z.pointMultiplicity p : ENNReal) + (d p : ENNReal) := h_ennreal_add p
    have hZ_fin : (Z.pointMultiplicity p : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have h : (Y.pointMultiplicity p : ENNReal) -
        (Z.pointMultiplicity p : ENNReal) = (d p : ENNReal) := by
      rw [h_eq1]
      exact ENNReal.add_sub_cancel_left hZ_fin
    exact h

  have h_mass_decomp : Y.mass = Z.mass + ∫⁻ p, d_enn p := by
    have h1 : Y.mass = ∫⁻ p, (Y.pointMultiplicity p : ENNReal) :=
      (lintegral_pointMultiplicity Y).symm
    rw [h1]
    have h2 : ∫⁻ p, (Y.pointMultiplicity p : ENNReal) =
        ∫⁻ p, ((Z.pointMultiplicity p : ENNReal) + d_enn p) := by
      congr with p
      have h3 : d_enn p = (d p : ENNReal) := h_d_enn_eq_d p
      rw [h3]
      exact h_ennreal_add p
    rw [h2]
    have hZ_enn : Measurable (fun p : Point3 => (Z.pointMultiplicity p : ENNReal)) :=
      (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp hZ_meas
    have h3 : ∫⁻ p, ((Z.pointMultiplicity p : ENNReal) + d_enn p) =
        (∫⁻ p, (Z.pointMultiplicity p : ENNReal)) + ∫⁻ p, d_enn p :=
      MeasureTheory.lintegral_add_left hZ_enn _
    rw [h3]
    have hZ_mass : (∫⁻ p, (Z.pointMultiplicity p : ENNReal)) = Z.mass :=
      lintegral_pointMultiplicity Z
    rw [hZ_mass]

  have hD_eq : ∫⁻ p, d_enn p = D := by
    have h' : Y.mass - Z.mass = ∫⁻ p, d_enn p := by
      rw [h_mass_decomp]
      exact ENNReal.add_sub_cancel_left hZ_mass_ne_top
    exact h'.symm

  have h_union_subset : ∀ (A B : WZ1PaperTubeShading F),
      PaperIsSubshading A B → A.union ⊆ B.union := by
    intro A B hsubAB p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hsubAB i hi⟩

  have h_on_B : ∀ p ∈ B, (Z.pointMultiplicity p : ENNReal) ≤ d_enn p := by
    intro p hp
    have h2 : 2 * Z.pointMultiplicity p < m := hp
    by_cases hZpos : 0 < Z.pointMultiplicity p
    · have h_in_Z : p ∈ Z.union := by
        have h_eq : Z.pointMultiplicity p =
            (Finset.univ.filter (fun i => p ∈ Z.carrier i)).card := by rfl
        have h15 : 0 < (Finset.univ.filter (fun i => p ∈ Z.carrier i)).card := by
          rw [← h_eq]
          exact hZpos
        rcases Finset.card_pos.mp h15 with ⟨i, hi⟩
        exact ⟨i, (Finset.mem_filter.mp hi).2⟩
      have h_in_Y : p ∈ Y.union := h_union_subset Z Y hsub h_in_Z
      have hY_ge : m ≤ Y.pointMultiplicity p := (hY_const p h_in_Y).1
      have h : Z.pointMultiplicity p ≤ d p := by
        dsimp only [d]
        omega
      rw [h_d_enn_eq_d p]
      exact_mod_cast h
    · have hZ0 : Z.pointMultiplicity p = 0 := by omega
      rw [hZ0]
      simp

  let mass_B := ∫⁻ p in B, (Z.pointMultiplicity p : ENNReal)
  let mass_S0 := ∫⁻ p in S0, (Z.pointMultiplicity p : ENNReal)
  let mass_S1 := ∫⁻ p in S1, (Z.pointMultiplicity p : ENNReal)

  have h_mass_B_le_D : mass_B ≤ D := by
    calc
      mass_B ≤ ∫⁻ p in B, d_enn p := by
        apply MeasureTheory.setLIntegral_mono' hB_meas
        intro p hp
        exact h_on_B p hp
      _ ≤ ∫⁻ p, d_enn p := MeasureTheory.setLIntegral_le_lintegral B d_enn
      _ = D := hD_eq

  have h_partition : ∀ p, p ∈ B ∨ p ∈ S0 ∨ p ∈ S1 := by
    intro p
    have h : 2 * Z.pointMultiplicity p < m ∨
        m ≤ 2 * Z.pointMultiplicity p := by omega
    rcases h with h | h
    · exact Or.inl h
    · by_cases h' : Z.pointMultiplicity p < m
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · have h'' : m ≤ Z.pointMultiplicity p := by omega
        exact Or.inr (Or.inr h'')

  have h_disj_BS0 : Disjoint B S0 := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    have h1 : 2 * Z.pointMultiplicity p < m := hp1
    have h2 : m ≤ 2 * Z.pointMultiplicity p := hp2.1
    omega
  have h_disj_BS1 : Disjoint B S1 := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    have h1 : 2 * Z.pointMultiplicity p < m := hp1
    have h2 : m ≤ Z.pointMultiplicity p := hp2
    have h3 : m ≤ 2 * Z.pointMultiplicity p := by linarith
    omega
  have h_disj_S0S1 : Disjoint S0 S1 := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    have h1 : Z.pointMultiplicity p < m := hp1.2
    have h2 : m ≤ Z.pointMultiplicity p := hp2
    omega

  have hS01_meas : MeasurableSet (S0 ∪ S1) := hS0_meas.union hS1_meas
  have h_disj_B_S01 : Disjoint B (S0 ∪ S1) :=
    h_disj_BS0.union_right h_disj_BS1

  have h_Z_mass_decomp : Z.mass = mass_B + mass_S0 + mass_S1 := by
    have h_univ : B ∪ (S0 ∪ S1) = Set.univ := by
      ext p
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      exact h_partition p
    have h3 : ∫⁻ p, (Z.pointMultiplicity p : ENNReal) =
        ∫⁻ p in B ∪ (S0 ∪ S1), (Z.pointMultiplicity p : ENNReal) := by
      rw [h_univ]
      simp
    have h21 : ∫⁻ p in B ∪ (S0 ∪ S1),
          (Z.pointMultiplicity p : ENNReal) =
        mass_B + ∫⁻ p in (S0 ∪ S1), (Z.pointMultiplicity p : ENNReal) :=
      MeasureTheory.lintegral_union hS01_meas h_disj_B_S01
    have h22 : ∫⁻ p in (S0 ∪ S1),
          (Z.pointMultiplicity p : ENNReal) =
        mass_S0 + mass_S1 := by
      rw [MeasureTheory.lintegral_union hS1_meas h_disj_S0S1]
    have h1 : ∫⁻ p, (Z.pointMultiplicity p : ENNReal) =
        mass_B + mass_S0 + mass_S1 := by
      rw [h3, h21, h22] <;> ring
    rw [lintegral_pointMultiplicity Z] at h1
    exact h1

  have h_Z_plus_D : Z.mass + D = Y.mass := by
    rw [h_mass_decomp, hD_eq]

  have h_2D_le : 2 * D ≤ (1 / 5 : ENNReal) * Y.mass := by
    have h10 : (1 / 10 : ENNReal) = ENNReal.ofReal (1 / 10 : ℝ) := by
      simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
    have h11 : (1 / 5 : ENNReal) = ENNReal.ofReal (1 / 5 : ℝ) := by
      simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
    calc
      2 * D ≤ 2 * (ENNReal.ofReal (1 / 10 : ℝ) * Y.mass) := by
        rw [h10] at hD_small <;> gcongr
      _ = ENNReal.ofReal (2 : ℝ) * (ENNReal.ofReal (1 / 10 : ℝ) * Y.mass) := by norm_cast
      _ = (ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (1 / 10 : ℝ)) * Y.mass := by rw [mul_assoc]
      _ = ENNReal.ofReal ((2 : ℝ) * (1 / 10 : ℝ)) * Y.mass := by rw [← ENNReal.ofReal_mul (by norm_num)]
      _ = ENNReal.ofReal (1 / 5 : ℝ) * Y.mass := by norm_num
      _ = (1 / 5 : ENNReal) * Y.mass := by rw [h11]

  have h_sum_plus_2D : Y.mass ≤ mass_S0 + mass_S1 + 2 * D := by
    have h1 : mass_S0 + mass_S1 + mass_B = Z.mass := by
      rw [h_Z_mass_decomp] <;> ring
    have h2 : Z.mass ≤ mass_S0 + mass_S1 + D := by
      calc
        Z.mass = mass_S0 + mass_S1 + mass_B := h1.symm
        _ ≤ mass_S0 + mass_S1 + D := by gcongr
    calc
      Y.mass = Z.mass + D := h_Z_plus_D.symm
      _ ≤ (mass_S0 + mass_S1 + D) + D := by gcongr
      _ = mass_S0 + mass_S1 + 2 * D := by ring

  have h_sum_lower :
      (4 / 5 : ENNReal) * Y.mass ≤ mass_S0 + mass_S1 := by
    have h_fin : (1 / 5 : ENNReal) * Y.mass ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hY_mass_ne_top
    apply (ENNReal.add_le_add_iff_right h_fin).mp
    calc
      (4 / 5 : ENNReal) * Y.mass + (1 / 5 : ENNReal) * Y.mass
        = ((4 / 5 : ENNReal) + (1 / 5 : ENNReal)) * Y.mass := by rw [add_mul]
      _ = (1 : ENNReal) * Y.mass := by
        have h1 : (4 / 5 : ENNReal) = ENNReal.ofReal (4 / 5 : ℝ) := by
          simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
        have h2 : (1 / 5 : ENNReal) = ENNReal.ofReal (1 / 5 : ℝ) := by
          simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
        have h : (4 / 5 : ENNReal) + (1 / 5 : ENNReal) = 1 := by
          rw [h1, h2]
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          <;> norm_num
        rw [h]
      _ = Y.mass := by rw [one_mul]
      _ ≤ mass_S0 + mass_S1 + 2 * D := h_sum_plus_2D
      _ ≤ mass_S0 + mass_S1 + (1 / 5 : ENNReal) * Y.mass := by gcongr

  have h_25_ne_top : (2 / 5 : ENNReal) * Y.mass ≠ ⊤ :=
    have h_ne_top : (2 / 5 : ENNReal) ≠ ⊤ := by
      apply ENNReal.div_ne_top <;> norm_num
    ENNReal.mul_ne_top h_ne_top hY_mass_ne_top

  have h_pigeonhole :
      (2 / 5 : ENNReal) * Y.mass ≤ mass_S0 ∨
        (2 / 5 : ENNReal) * Y.mass ≤ mass_S1 := by
    by_contra h
    push Not at h
    have h1 : mass_S0 < (2 / 5 : ENNReal) * Y.mass := h.1
    have h2 : mass_S1 < (2 / 5 : ENNReal) * Y.mass := h.2
    have h_le_S1 : mass_S1 ≤ Z.mass := by
      calc
        mass_S1 ≤ ∫⁻ p, (Z.pointMultiplicity p : ENNReal) :=
          MeasureTheory.setLIntegral_le_lintegral S1 _
        _ = Z.mass := lintegral_pointMultiplicity Z
    have h_S1_ne_top : mass_S1 ≠ ⊤ :=
      ne_top_of_le_ne_top hZ_mass_ne_top h_le_S1
    have h3 : mass_S0 + mass_S1 < (4 / 5 : ENNReal) * Y.mass := by
      calc
        mass_S0 + mass_S1
            < (2 / 5 : ENNReal) * Y.mass + mass_S1 :=
          ENNReal.add_lt_add_right h_S1_ne_top h1
        _ < (2 / 5 : ENNReal) * Y.mass + (2 / 5 : ENNReal) * Y.mass :=
          ENNReal.add_lt_add_left h_25_ne_top h2
        _ = ((2 / 5 : ENNReal) + (2 / 5 : ENNReal)) * Y.mass := by rw [add_mul]
        _ = (4 / 5 : ENNReal) * Y.mass := by
          have h1 : (2 / 5 : ENNReal) = ENNReal.ofReal (2 / 5 : ℝ) := by
            simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
          have h2 : (4 / 5 : ENNReal) = ENNReal.ofReal (4 / 5 : ℝ) := by
            simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
          have h : (2 / 5 : ENNReal) + (2 / 5 : ENNReal) = (4 / 5 : ENNReal) := by
            rw [h1, h2]
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            <;> norm_num
          rw [h]
    exact (not_lt_of_ge h_sum_lower) h3

  rcases h_pigeonhole with hS0 | hS1
  · let a := (m + 1) / 2
    let W := paperRestrictShadingToSet Z S0 hS0_meas
    have h_W_sub : PaperIsSubshading W Z := by
      intro j x hx
      exact hx.1
    have h_W_const : W.HasConstantMultiplicity a (2 * a) := by
      intro p hp
      have h_in_S0 : p ∈ S0 := by
        rcases hp with ⟨j, hj⟩
        exact hj.2
      have h_eq : W.pointMultiplicity p = Z.pointMultiplicity p :=
        paperPmRestrictShadingToSet hS0_meas h_in_S0
      rw [h_eq]
      have h3 : m ≤ 2 * Z.pointMultiplicity p := h_in_S0.1
      have h4 : Z.pointMultiplicity p < m := h_in_S0.2
      have h5 : a ≤ Z.pointMultiplicity p := by
        dsimp only [a]
        omega
      have h6 : Z.pointMultiplicity p < 2 * a := by
        dsimp only [a]
        omega
      exact ⟨h5, by omega⟩
    have h_W_mass : W.mass = mass_S0 :=
      paperMassRestrictShadingToSet hS0_meas
    have h_mass : (1 / 4 : ENNReal) * Y.mass ≤ W.mass := by
      rw [h_W_mass]
      have h1 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by
        simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
      have h2 : (2 / 5 : ENNReal) = ENNReal.ofReal (2 / 5 : ℝ) := by
        simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
      have h : (1 / 4 : ENNReal) ≤ (2 / 5 : ENNReal) := by
        rw [h1, h2]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      have h' : (1 / 4 : ENNReal) * Y.mass ≤ (2 / 5 : ENNReal) * Y.mass :=
        mul_le_mul_of_nonneg_right h (by simp)
      exact h'.trans hS0
    have h_W_cubical : WZ1PaperIsCubicalShading W := by
      apply paperRestrictShadingToSet_cubical hS0_meas hZ_cubical
      intro p hp q hq
      have hsame : wz1PaperGridIndex delta p =
          wz1PaperGridIndex delta q :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta p) q).mp hq |>.symm
      have heq := hZ_multiplicity_same_cell hsame
      change m ≤ 2 * Z.pointMultiplicity q ∧ Z.pointMultiplicity q < m
      exact ⟨by rw [← heq]; exact hp.1, by rw [← heq]; exact hp.2⟩
    exact ⟨a, W, h_W_sub, h_W_const, by dsimp only [a]; omega, h_mass,
      h_W_cubical⟩
  · let a := m
    let W := paperRestrictShadingToSet Z S1 hS1_meas
    have h_W_sub : PaperIsSubshading W Z := by
      intro j x hx
      exact hx.1
    have h_W_const : W.HasConstantMultiplicity a (2 * a) := by
      intro p hp
      have h_in_S1 : p ∈ S1 := by
        rcases hp with ⟨j, hj⟩
        exact hj.2
      rw [paperPmRestrictShadingToSet hS1_meas h_in_S1]
      have h_in_Y : p ∈ Y.union := by
        rcases hp with ⟨j, hj⟩
        exact h_union_subset Z Y hsub ⟨j, hj.1⟩
      exact ⟨h_in_S1, (h_ge p).trans (hY_const p h_in_Y).2⟩
    have h_W_mass : W.mass = mass_S1 :=
      paperMassRestrictShadingToSet hS1_meas
    have h_mass : (1 / 4 : ENNReal) * Y.mass ≤ W.mass := by
      rw [h_W_mass]
      have h1 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by
        simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
      have h2 : (2 / 5 : ENNReal) = ENNReal.ofReal (2 / 5 : ℝ) := by
        simp [div_eq_mul_inv] <;> norm_cast <;> norm_num
      have h : (1 / 4 : ENNReal) ≤ (2 / 5 : ENNReal) := by
        rw [h1, h2]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      have h' : (1 / 4 : ENNReal) * Y.mass ≤ (2 / 5 : ENNReal) * Y.mass :=
        mul_le_mul_of_nonneg_right h (by simp)
      exact h'.trans hS1
    have h_W_cubical : WZ1PaperIsCubicalShading W := by
      apply paperRestrictShadingToSet_cubical hS1_meas hZ_cubical
      intro p hp q hq
      have hsame : wz1PaperGridIndex delta p =
          wz1PaperGridIndex delta q :=
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta p) q).mp hq |>.symm
      change m ≤ Z.pointMultiplicity q
      rw [← hZ_multiplicity_same_cell hsame]
      exact hp
    exact ⟨a, W, h_W_sub, h_W_const, by dsimp only [a]; omega, h_mass,
      h_W_cubical⟩

/-!
## Direction non-concentration

The coarse direction packing theorem is UTS-free and depends only on
essential distinctness.
-/

/--
Direction non-concentration for the PureWZ2 coarse family.

Follows from essential distinctness: the number of essentially distinct
tubes within angle `10*L` of a given direction at a point is universally
bounded by `D = 2 * 4 * 601^3 * 12001^3`.

TODO: apply `wz1_coarse_direction_packing` to the coarse family.
-/
lemma pureWz2_close_direction_count
    {delta sigma L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (h_essentially_distinct : WZ1PaperIsEssentiallyDistinct coarse)
    (h_line_class : WZ1PaperIsLineClass coarse)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000) :
    ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (i : Fin coarse.card),
        p ∈ coarseShading.carrier i →
          (paperCloseDirectionCount coarseShading p i (10 * L) : ENNReal) ≤
            (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) := by
  intro p _ i hi
  let S : Finset (Fin coarse.card) := Finset.univ.filter fun j =>
    p ∈ coarseShading.carrier j ∧
      ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ < 10 * L
  have h1 : ∀ j ∈ S, wz1PaperLineDistance (coarse.tube j) (coarse.tube i) ≤ 500 * L := by
    intro j hj
    have h2 : p ∈ coarseShading.carrier j ∧
        ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ < 10 * L :=
      (Finset.mem_filter.mp hj).2
    exact paper_line_distance_shared_point hL_pos hL_small
      (h_line_class i) (h_line_class j) p
      (coarseShading.subset_body i hi)
      (coarseShading.subset_body j h2.1)
      h2.2
  let T : Finset (Fin coarse.card) := Finset.univ.filter fun j =>
    wz1PaperLineDistance (coarse.tube j) (coarse.tube i) ≤ 500 * L
  have h3 : S ⊆ T := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1 j hj⟩
  have h4 : S.card ≤ T.card := Finset.card_le_card h3
  have h5 : T.card ≤ (2 * Nat.ceil (8 * (500 * L) / L) + 1)^5 :=
    tube_packing_bound_general h_essentially_distinct h_line_class hL_pos
      (500 * L) (by positivity) i
  have h6 : (2 * Nat.ceil (8 * (500 * L) / L) + 1)^5 = 8001^5 := by
    have h7 : 8 * (500 * L) / L = 4000 := by
      field_simp [hL_pos.ne'] <;> ring
    rw [h7] <;> norm_num
  rw [h6] at h5
  have h7 : S.card ≤ 8001^5 := le_trans h4 h5
  have h8 : (S.card : ENNReal) ≤ (8001^5 : ENNReal) := by exact_mod_cast h7
  have h9 : (8001^5 : ENNReal) ≤ (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) := by
    norm_num
  have h10 : paperCloseDirectionCount coarseShading p i (10 * L) = S.card := by
    rfl
  rw [h10]
  exact h8.trans h9

/--
Generalized direction non-concentration for the PureWZ2 coarse family.

Uses threshold `K*L` instead of `10*L`, with close-direction count bounded
by `(1600*K + 1)^5`. This is needed for the Córdoba constant fix: choosing
a larger kappa threshold increases the count polynomially in K, while the
multiplicity capacity grows as L^-1, so for small L we can afford K ≈ 50000.
-/
lemma pureWz2_close_direction_count_general
    {delta sigma L : ℝ} {K : ℕ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (h_essentially_distinct : WZ1PaperIsEssentiallyDistinct coarse)
    (h_line_class : WZ1PaperIsLineClass coarse)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (hK_one : 1 ≤ K) (hKL_small : (K : ℝ) * L ≤ 1 / 2) :
    ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (i : Fin coarse.card),
        p ∈ coarseShading.carrier i →
          (paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) : ENNReal) ≤
            ((1600 * K + 1)^5 : ENNReal) := by
  intro p _ i hi
  let kappa : ℝ := (K : ℝ) * L
  let S : Finset (Fin coarse.card) := Finset.univ.filter fun j =>
    p ∈ coarseShading.carrier j ∧
      ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ < kappa
  have h1 : ∀ j ∈ S, wz1PaperLineDistance (coarse.tube j) (coarse.tube i) ≤ 100 * kappa := by
    intro j hj
    have h2 : p ∈ coarseShading.carrier j ∧
        ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ < kappa :=
      (Finset.mem_filter.mp hj).2
    have hK_one' : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK_one
    have h_cross' : ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ < (K : ℝ) * L := by
      simpa [kappa] using h2.2
    have h_final : wz1PaperLineDistance (coarse.tube j) (coarse.tube i) ≤ 100 * kappa := by
      have h_res := paper_line_distance_shared_point_general hL_pos hL_small hK_one' hKL_small
        (h_line_class i) (h_line_class j) p
        (coarseShading.subset_body i hi)
        (coarseShading.subset_body j h2.1)
        h_cross'
      have h_eq : (100 * (K : ℝ) * L) = 100 * kappa := by
        simp only [kappa] <;> ring
      rw [h_eq] at h_res
      exact h_res
    exact h_final
  let T : Finset (Fin coarse.card) := Finset.univ.filter fun j =>
    wz1PaperLineDistance (coarse.tube j) (coarse.tube i) ≤ 100 * kappa
  have h3 : S ⊆ T := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1 j hj⟩
  have h4 : S.card ≤ T.card := Finset.card_le_card h3
  have h5 : T.card ≤ (2 * Nat.ceil (8 * (100 * kappa) / L) + 1)^5 :=
    tube_packing_bound_general h_essentially_distinct h_line_class hL_pos
      (100 * kappa) (by positivity) i
  have h6 : 8 * (100 * kappa) / L = 800 * (K : ℝ) := by
    dsimp only [kappa]
    field_simp [hL_pos.ne'] <;> ring
  rw [h6] at h5
  have h7 : Nat.ceil (800 * (K : ℝ)) = 800 * K := by
    rw [Nat.ceil_eq_iff] <;> norm_cast <;> omega
  rw [h7] at h5
  have h8 : S.card ≤ (1600 * K + 1)^5 := by
    have h81 : (2 * (800 * K) + 1) = 1600 * K + 1 := by ring
    rw [h81] at h5
    exact h4.trans h5
  have h9 : (S.card : ENNReal) ≤ ((1600 * K + 1)^5 : ENNReal) := by exact_mod_cast h8
  have h10 : paperCloseDirectionCount coarseShading p i kappa = S.card := by rfl
  rw [h10]
  exact h9

/--
Paper-shading transverse selection: if the close-direction count in a
super-shading is strictly below the lower multiplicity, some active tube
is transverse.
-/
lemma paperTransverseFromCloseCountLtMultiplicity
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : WZ1PaperTubeShading F} {m : ℕ}
    (p : Point3) (hp : p ∈ Z.union)
    (hm_lower : m ≤ Z.pointMultiplicity p)
    (hsub : PaperIsSubshading Z Y)
    (i : Fin F.card) (kappa : ℝ)
    (hclose : (paperCloseDirectionCount Y p i kappa : ENNReal) < (m : ENNReal)) :
    ∃ j : Fin F.card,
      p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
  classical
  let active : Finset (Fin F.card) :=
    Finset.univ.filter fun j => p ∈ Z.carrier j
  let close : Finset (Fin F.card) :=
    active.filter fun j =>
      ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa
  have hactiveCard : active.card = Z.pointMultiplicity p := by rfl
  have hmActive : m ≤ active.card := by
    rw [hactiveCard]
    exact hm_lower
  have hcloseSubset :
      close ⊆ Finset.univ.filter fun j =>
        p ∈ Y.carrier j ∧
          ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa := by
    intro j hj
    have hjActive : j ∈ active := (Finset.mem_filter.mp hj).1
    have hjZ : p ∈ Z.carrier j := (Finset.mem_filter.mp hjActive).2
    have hjClose : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa :=
      (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hsub j hjZ, hjClose⟩
  have hcloseCard : close.card < m := by
    have hle : close.card ≤ paperCloseDirectionCount Y p i kappa :=
      Finset.card_le_card hcloseSubset
    have hlt : paperCloseDirectionCount Y p i kappa < m := by exact_mod_cast hclose
    exact hle.trans_lt hlt
  have hcard : close.card < active.card := by
    calc close.card < m := hcloseCard
      _ ≤ active.card := hmActive
  have hexists : ∃ j, j ∈ active \ close := by
    by_contra h
    have hsub2 : active ⊆ close := by
      intro j hj
      by_cases hc : j ∈ close
      · exact hc
      · have h' : j ∈ active \ close := Finset.mem_sdiff.mpr ⟨hj, hc⟩
        exact False.elim (h ⟨j, h'⟩)
    have h9 : active.card ≤ close.card := Finset.card_le_card hsub2
    linarith
  rcases hexists with ⟨j, hj⟩
  have hjActive : j ∈ active := (Finset.mem_sdiff.mp hj).1
  have hjNotClose : j ∉ close := (Finset.mem_sdiff.mp hj).2
  have hjZ : p ∈ Z.carrier j := (Finset.mem_filter.mp hjActive).2
  have htrans : kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
    by_contra h
    have h' : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa := by linarith
    have hjClose : j ∈ close := by
      exact Finset.mem_filter.mpr ⟨hjActive, h'⟩
    exact hjNotClose hjClose
  exact ⟨j, hjZ, htrans⟩

/-!
## Property-(P) refinement theorem

Constructs `PureWZ2PropertyPData` from the sticky data.

Steps:
1. Grid-cell prune the coarse shading for local fullness
2. Extract constant multiplicity via two-level extraction
3. Restore volume upper from the coarse extremal reference
4. Use direction non-concentration + multiplicity margin for transverse selection
-/

/--
Construct property-(P) data from the PureWZ2 sticky configuration.

This is the HIGH-multiplicity case: given `m > D` such that
`m * volume(union) < mass`, the high-multiplicity set is nonempty, and we
restrict the shading to it. The resulting propertyOne is nonempty, has
pointwise multiplicity ≥ m, and satisfies the transverse condition because
the close-direction count is bounded by D < m.

The LOW-multiplicity case (when no such m exists) is handled separately
by the local AD dichotomy.
-/
def pureWz2_propertyP_refinement
    {delta sigma outputLoss L tau : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss coarse coarseShading)
    (h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i))
    (epsilon₁ epsilon₃ : ℝ)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_large : L * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (m : ℕ)
    (hm_pos : 0 < m)
    (hm_gt_packing :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (h_mass_ne_top : coarseShading.mass ≠ ⊤)
    (h_volume_ne_top : volume coarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass)
    (h_kappa : Real.rpow L epsilon₃ ≤ 10 * L)
    (h_cell_full :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
      Kakeya.realRpowENN L 3) :
    PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) := by
  classical
  let D : ENNReal := 2 * 4 * 601 ^ 3 * 12001 ^ 3
  let S : Set Point3 := paperHighMultiplicitySet coarseShading (m : ENNReal)
  have hS_meas : MeasurableSet S :=
    measurableSet_paperHighMultiplicitySet coarseShading (m : ENNReal)
  have hS_nonempty : S.Nonempty :=
    paperHighMultiplicitySet_nonempty h_mass_ne_top h_volume_ne_top
      (h_avg.trans_le (by
        have hhalf : (1 / 2 : ENNReal) ≤ 1 := by norm_num
        simpa using mul_le_mul_right' hhalf coarseShading.mass))
  let propertyOne : WZ1PaperTubeShading coarse :=
    paperRestrictShadingToSet coarseShading S hS_meas
  have h_propertyOne_sub : PaperIsSubshading propertyOne coarseShading := by
    intro i p hp
    exact hp.1
  have h_propertyOne_mass :
      (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyOne.mass := by
    simpa [propertyOne, S] using
      paperHighMultiplicityRestriction_half_mass h_mass_ne_top h_avg
  have h_union_eq : propertyOne.union = S := by
    ext p
    simp only [propertyOne, paperRestrictShadingToSet,
      Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact hi.2
    · intro hp
      have h_p_in_union : p ∈ coarseShading.union := hp.1
      rcases h_p_in_union with ⟨i, hi⟩
      exact ⟨i, hi, hp⟩
  have h_pointwise : ∀ p ∈ propertyOne.union,
      m ≤ propertyOne.pointMultiplicity p := by
    intro p hp
    have h_p_in_S : p ∈ S := by rw [h_union_eq] at hp; exact hp
    have h1 : (m : ENNReal) ≤ (coarseShading.pointMultiplicity p : ENNReal) :=
      h_p_in_S.2
    have h2 : propertyOne.pointMultiplicity p = coarseShading.pointMultiplicity p :=
      paperPmRestrictShadingToSet hS_meas h_p_in_S
    rw [h2]
    exact_mod_cast h1
  have h_full : ∀ (j : Fin coarse.card) (p : Point3),
      p ∈ propertyOne.carrier j →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        volume (propertyOne.carrier j ∩ Metric.closedBall p tau) := by
    intro j p hp
    have h_p_in_S : p ∈ S := hp.2
    have h_carrier_eq : propertyOne.carrier j = coarseShading.carrier j ∩ S := by rfl
    rw [h_carrier_eq]
    have h5 : volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau) ≥
        Kakeya.realRpowENN L 3 := by
      let cell := wz1PaperGridIndex L p
      let cube := wz1PaperGridCube L cell
      have h_p_in_cube : p ∈ cube := by
        rw [mem_wz1PaperGridCube L cell p] <;> rfl
      have h_cube_sub_carrier : cube ⊆ coarseShading.carrier j :=
        coarseExtremal.cubical j p hp.1
      have h_same_index : ∀ q ∈ cube, wz1PaperGridIndex L q = cell := by
        intro q hq
        exact (mem_wz1PaperGridCube L cell q).mp hq
      have h_cube_sub_S : cube ⊆ S := by
        intro q hq
        have h1 : ∀ (i : Fin coarse.card),
            p ∈ coarseShading.carrier i ↔ q ∈ coarseShading.carrier i := by
          intro i
          constructor
          · intro hpi
            exact (coarseExtremal.cubical i p hpi) hq
          · intro hqi
            have h_cube_q : wz1PaperGridCube L (wz1PaperGridIndex L q) ⊆ coarseShading.carrier i :=
              coarseExtremal.cubical i q hqi
            have h_idx : wz1PaperGridIndex L q = cell := h_same_index q hq
            rw [h_idx] at h_cube_q
            exact h_cube_q h_p_in_cube
        have h2 : p ∈ coarseShading.union := ⟨j, hp.1⟩
        have h3 : q ∈ coarseShading.union := by
          rcases h2 with ⟨i, hi⟩
          exact ⟨i, (h1 i).mp hi⟩
        have h4 : coarseShading.pointMultiplicity p = coarseShading.pointMultiplicity q := by
          dsimp only [Kakeya.Streamlined.Shading.pointMultiplicity]
          congr
          ext i
          exact h1 i
        have h5 : (m : ENNReal) ≤ (coarseShading.pointMultiplicity p : ENNReal) :=
          h_p_in_S.2
        exact ⟨h3, by rw [←h4]; exact h5⟩
      have h_cube_sub_ball : cube ⊆ Metric.closedBall p tau := by
        intro q hq
        let box : Set Point3 := {r |
            (cell.1 : ℝ) * L ≤ r 0 ∧ r 0 < ((cell.1 : ℝ) + 1) * L ∧
            (cell.2.1 : ℝ) * L ≤ r 1 ∧ r 1 < ((cell.2.1 : ℝ) + 1) * L ∧
            (cell.2.2 : ℝ) * L ≤ r 2 ∧ r 2 < ((cell.2.2 : ℝ) + 1) * L}
        have h_eq_ico : cube = box := wz1PaperGridCube_eq_Ico hL_pos cell
        have hbp : p ∈ box := by rw [←h_eq_ico]; exact h_p_in_cube
        have hbq : q ∈ box := by rw [←h_eq_ico]; exact hq
        rcases hbp with ⟨hbp0_lo, hbp0_hi, hbp1_lo, hbp1_hi, hbp2_lo, hbp2_hi⟩
        rcases hbq with ⟨hbq0_lo, hbq0_hi, hbq1_lo, hbq1_hi, hbq2_lo, hbq2_hi⟩
        have h60 : |q 0 - p 0| < L := by
          rw [abs_sub_lt_iff] <;> constructor <;> linarith
        have h61 : |q 1 - p 1| < L := by
          rw [abs_sub_lt_iff] <;> constructor <;> linarith
        have h62 : |q 2 - p 2| < L := by
          rw [abs_sub_lt_iff] <;> constructor <;> linarith
        have h6 : ∀ (i : Fin 3), |q i - p i| < L := by
          intro i
          fin_cases i <;> simp [abs_lt] <;> constructor <;> linarith
        have h10 : dist q p ^ 2 = ∑ i : Fin 3, (q i - p i) ^ 2 := by
          have h11 : dist q p = ‖q - p‖ := by rfl
          rw [h11]
          exact EuclideanSpace.real_norm_sq_eq (q - p)
        have h12 : ∀ i : Fin 3, (q i - p i) ^ 2 < L ^ 2 := by
          intro i
          have h13 : |q i - p i| < L := h6 i
          nlinarith [abs_lt.mp h13]
        have h11 : ∑ i : Fin 3, (q i - p i) ^ 2 < 3 * L ^ 2 := by
          have h_sum3 : ∑ i : Fin 3, (q i - p i) ^ 2 =
              (q 0 - p 0)^2 + (q 1 - p 1)^2 + (q 2 - p 2)^2 := by
            simp [Fin.sum_univ_succ] <;> ring
          rw [h_sum3]
          linarith [h12 0, h12 1, h12 2]
        have h15 : dist q p < L * Real.sqrt 3 := by
          have h16 : dist q p ^ 2 < (L * Real.sqrt 3) ^ 2 := by
            rw [h10]
            have h17 : (L * Real.sqrt 3) ^ 2 = 3 * L ^ 2 := by
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            rw [h17]
            exact h11
          have h18 : 0 ≤ dist q p := dist_nonneg
          have h19 : 0 ≤ L * Real.sqrt 3 := by positivity
          nlinarith
        have h20 : dist q p ≤ tau := le_trans h15.le htau_large
        exact h20
      have h_cube_sub : cube ⊆ coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau := by
        intro q hq
        have h_a : q ∈ coarseShading.carrier j := h_cube_sub_carrier hq
        have h_b : q ∈ S := h_cube_sub_S hq
        have h_c : q ∈ Metric.closedBall p tau := h_cube_sub_ball hq
        exact Set.mem_inter (Set.mem_inter h_a h_b) h_c
      have h_volume_cube : volume cube = Kakeya.realRpowENN L 3 := by
        have h1 : volume cube = volume (wz1PaperGridCube L (0, 0, 0)) :=
          wz1PaperGridCube_volume_eq hL_pos cell (0, 0, 0)
        rw [h1]
        have h2 : volume (wz1PaperGridCube L (0, 0, 0)) = ENNReal.ofReal (L ^ 3) :=
          wz1PaperGridCube_volume_exact hL_pos
        rw [h2]
        have h4 : Kakeya.realRpowENN L 3 = ENNReal.ofReal (L ^ 3) := by
          simp [Kakeya.realRpowENN, Real.rpow_natCast] <;> rfl
        exact h4.symm
      calc
        volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau)
          ≥ volume cube := measure_mono h_cube_sub
        _ = Kakeya.realRpowENN L 3 := h_volume_cube
    calc
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau
        ≤ Kakeya.realRpowENN L 3 := h_cell_full
      _ ≤ volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau) := h5
  let propertyThree : WZ1PaperTubeShading coarse := propertyOne
  have h_transverse : ∀ p ∈ propertyThree.union,
      ∀ (i : Fin coarse.card),
        p ∈ propertyThree.carrier i →
          ∃ (j : Fin coarse.card),
            p ∈ propertyOne.carrier j ∧
              Real.rpow L epsilon₃ ≤
                ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ := by
    intro p hp i hi
    have h_p_in_S : p ∈ S := by rw [h_union_eq] at hp; exact hp
    have h_mult : m ≤ propertyOne.pointMultiplicity p := h_pointwise p hp
    have h_close : (paperCloseDirectionCount coarseShading p i (10 * L) : ENNReal) ≤ D :=
      pureWz2_close_direction_count (delta := delta) (sigma := sigma) (L := L)
        cover.coarse_essentially_distinct
        h_line
        hL_pos hL_small p (by
          have h_p_in_S : p ∈ S := by rw [←h_union_eq]; exact hp
          exact h_p_in_S.1)
        i (by
          have h6 : p ∈ coarseShading.carrier i := hi.1
          exact h6)
    have h_close_lt : (paperCloseDirectionCount coarseShading p i (10 * L) : ENNReal) < (m : ENNReal) :=
      h_close.trans_lt hm_gt_packing
    rcases paperTransverseFromCloseCountLtMultiplicity
        p hp h_mult h_propertyOne_sub i (10 * L) h_close_lt with ⟨j, hj1, hj2⟩
    refine ⟨j, hj1, ?_⟩
    have h7 : Real.rpow L epsilon₃ ≤ 10 * L := h_kappa
    have h8 : 10 * L ≤ ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ := hj2
    exact h7.trans h8
  exact
    { propertyOne := propertyOne
      propertyOne_sub := h_propertyOne_sub
      propertyOne_mass := h_propertyOne_mass
      propertyThree := propertyThree
      propertyThree_sub := by
        intro i
        exact Set.Subset.refl _
      propertyThree_common_spatial := by
        intro i
        change coarseShading.carrier i ∩ S =
          coarseShading.carrier i ∩ propertyOne.union
        rw [h_union_eq]
      propertyThree_mass := h_propertyOne_mass
      propertyThree_cubical :=
        paperHighMultiplicityRestriction_cubical coarseExtremal.cubical
      multiplicity := m
      multiplicity_pos := hm_pos
      multiplicity_lower_pointwise := h_pointwise
      multiplicity_gt_packing := hm_gt_packing
      propertyOne_full := h_full
      transverse := h_transverse }

/--
Generalized property-(P) refinement with arbitrary kappa threshold K*L.

Uses `paper_line_distance_shared_point_general` and `pureWz2_close_direction_count_general`
to support a larger kappa threshold, which helps resolve the Córdoba parameter
incompatibility. Takes both the original `hm_gt_packing` (for the structure field)
and a stronger `hm_gt_general` (for the transverse proof when K is large).
-/
def pureWz2_propertyP_refinement_general_of_close_count_lt
    {sigma outputLoss L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss coarse coarseShading)
    (h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i))
    (epsilon₁ epsilon₃ : ℝ)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_large : L * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (K : ℕ)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * L ≤ 1 / 2)
    (m : ℕ)
    (h_close_count : ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (i : Fin coarse.card),
        p ∈ coarseShading.carrier i →
          (paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) :
              ENNReal) < (m : ENNReal))
    (hm_pos : 0 < m)
    (hm_gt_packing :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (h_mass_ne_top : coarseShading.mass ≠ ⊤)
    (h_volume_ne_top : volume coarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass)
    (h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L)
    (h_cell_full :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
      Kakeya.realRpowENN L 3) :
    PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) := by
  classical
  let D : ENNReal := 2 * 4 * 601 ^ 3 * 12001 ^ 3
  let kappa : ℝ := (K : ℝ) * L
  let S : Set Point3 := paperHighMultiplicitySet coarseShading (m : ENNReal)
  have hS_meas : MeasurableSet S :=
    measurableSet_paperHighMultiplicitySet coarseShading (m : ENNReal)
  have hS_nonempty : S.Nonempty :=
    paperHighMultiplicitySet_nonempty h_mass_ne_top h_volume_ne_top
      (h_avg.trans_le (by
        have hhalf : (1 / 2 : ENNReal) ≤ 1 := by norm_num
        simpa using mul_le_mul_right' hhalf coarseShading.mass))
  let propertyOne : WZ1PaperTubeShading coarse :=
    paperRestrictShadingToSet coarseShading S hS_meas
  have h_propertyOne_sub : PaperIsSubshading propertyOne coarseShading := by
    intro i p hp
    exact hp.1
  have h_propertyOne_mass :
      (1 / 2 : ENNReal) * coarseShading.mass ≤ propertyOne.mass := by
    simpa [propertyOne, S] using
      paperHighMultiplicityRestriction_half_mass h_mass_ne_top h_avg
  have h_union_eq : propertyOne.union = S := by
    ext p
    simp only [propertyOne, paperRestrictShadingToSet,
      Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact hi.2
    · intro hp
      have h_p_in_union : p ∈ coarseShading.union := hp.1
      rcases h_p_in_union with ⟨i, hi⟩
      exact ⟨i, hi, hp⟩
  have h_pointwise : ∀ p ∈ propertyOne.union,
      m ≤ propertyOne.pointMultiplicity p := by
    intro p hp
    have h_p_in_S : p ∈ S := by rw [h_union_eq] at hp; exact hp
    have h1 : (m : ENNReal) ≤ (coarseShading.pointMultiplicity p : ENNReal) :=
      h_p_in_S.2
    have h2 : propertyOne.pointMultiplicity p = coarseShading.pointMultiplicity p :=
      paperPmRestrictShadingToSet hS_meas h_p_in_S
    rw [h2]
    exact_mod_cast h1
  have h_full : ∀ (j : Fin coarse.card) (p : Point3),
      p ∈ propertyOne.carrier j →
        Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        volume (propertyOne.carrier j ∩ Metric.closedBall p tau) := by
    intro j p hp
    have h_p_in_S : p ∈ S := hp.2
    have h_carrier_eq : propertyOne.carrier j = coarseShading.carrier j ∩ S := by rfl
    rw [h_carrier_eq]
    have h5 : volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau) ≥
        Kakeya.realRpowENN L 3 := by
      let cell := wz1PaperGridIndex L p
      let cube := wz1PaperGridCube L cell
      have h_p_in_cube : p ∈ cube := by
        rw [mem_wz1PaperGridCube L cell p] <;> rfl
      have h_cube_sub_carrier : cube ⊆ coarseShading.carrier j :=
        coarseExtremal.cubical j p hp.1
      have h_same_index : ∀ q ∈ cube, wz1PaperGridIndex L q = cell := by
        intro q hq
        exact (mem_wz1PaperGridCube L cell q).mp hq
      have h_cube_sub_S : cube ⊆ S := by
        intro q hq
        have h1 : ∀ (i : Fin coarse.card),
            p ∈ coarseShading.carrier i ↔ q ∈ coarseShading.carrier i := by
          intro i
          constructor
          · intro hpi
            exact (coarseExtremal.cubical i p hpi) hq
          · intro hqi
            have h_cube_q : wz1PaperGridCube L (wz1PaperGridIndex L q) ⊆ coarseShading.carrier i :=
              coarseExtremal.cubical i q hqi
            have h_idx : wz1PaperGridIndex L q = cell := h_same_index q hq
            rw [h_idx] at h_cube_q
            exact h_cube_q h_p_in_cube
        have h2 : p ∈ coarseShading.union := ⟨j, hp.1⟩
        have h3 : q ∈ coarseShading.union := by
          rcases h2 with ⟨i, hi⟩
          exact ⟨i, (h1 i).mp hi⟩
        have h4 : coarseShading.pointMultiplicity p = coarseShading.pointMultiplicity q := by
          dsimp only [Kakeya.Streamlined.Shading.pointMultiplicity]
          congr
          ext i
          exact h1 i
        have h5 : (m : ENNReal) ≤ (coarseShading.pointMultiplicity p : ENNReal) :=
          h_p_in_S.2
        exact ⟨h3, by rw [←h4]; exact h5⟩
      have h_cube_sub_ball : cube ⊆ Metric.closedBall p tau := by
        intro q hq
        let box : Set Point3 := {r |
            (cell.1 : ℝ) * L ≤ r 0 ∧ r 0 < ((cell.1 : ℝ) + 1) * L ∧
            (cell.2.1 : ℝ) * L ≤ r 1 ∧ r 1 < ((cell.2.1 : ℝ) + 1) * L ∧
            (cell.2.2 : ℝ) * L ≤ r 2 ∧ r 2 < ((cell.2.2 : ℝ) + 1) * L}
        have h_eq_ico : cube = box := wz1PaperGridCube_eq_Ico hL_pos cell
        have hbp : p ∈ box := by rw [←h_eq_ico]; exact h_p_in_cube
        have hbq : q ∈ box := by rw [←h_eq_ico]; exact hq
        rcases hbp with ⟨hbp0_lo, hbp0_hi, hbp1_lo, hbp1_hi, hbp2_lo, hbp2_hi⟩
        rcases hbq with ⟨hbq0_lo, hbq0_hi, hbq1_lo, hbq1_hi, hbq2_lo, hbq2_hi⟩
        have h6 : ∀ (i : Fin 3), |q i - p i| < L := by
          intro i
          fin_cases i <;> simp [abs_lt] <;> constructor <;> linarith
        have h10 : dist q p ^ 2 = ∑ i : Fin 3, (q i - p i) ^ 2 := by
          have h11 : dist q p = ‖q - p‖ := by rfl
          rw [h11]
          exact EuclideanSpace.real_norm_sq_eq (q - p)
        have h12 : ∀ i : Fin 3, (q i - p i) ^ 2 < L ^ 2 := by
          intro i
          have h13 : |q i - p i| < L := h6 i
          nlinarith [abs_lt.mp h13]
        have h11 : ∑ i : Fin 3, (q i - p i) ^ 2 < 3 * L ^ 2 := by
          have h_sum3 : ∑ i : Fin 3, (q i - p i) ^ 2 =
              (q 0 - p 0)^2 + (q 1 - p 1)^2 + (q 2 - p 2)^2 := by
            simp [Fin.sum_univ_succ] <;> ring
          rw [h_sum3]
          linarith [h12 0, h12 1, h12 2]
        have h15 : dist q p < L * Real.sqrt 3 := by
          have h16 : dist q p ^ 2 < (L * Real.sqrt 3) ^ 2 := by
            rw [h10]
            have h17 : (L * Real.sqrt 3) ^ 2 = 3 * L ^ 2 := by
              nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            rw [h17]
            exact h11
          have h18 : 0 ≤ dist q p := dist_nonneg
          have h19 : 0 ≤ L * Real.sqrt 3 := by positivity
          nlinarith
        have h20 : dist q p ≤ tau := le_trans h15.le htau_large
        exact h20
      have h_cube_sub : cube ⊆ coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau := by
        intro q hq
        have h_a : q ∈ coarseShading.carrier j := h_cube_sub_carrier hq
        have h_b : q ∈ S := h_cube_sub_S hq
        have h_c : q ∈ Metric.closedBall p tau := h_cube_sub_ball hq
        exact Set.mem_inter (Set.mem_inter h_a h_b) h_c
      have h_volume_cube : volume cube = Kakeya.realRpowENN L 3 := by
        have h1 : volume cube = volume (wz1PaperGridCube L (0, 0, 0)) :=
          wz1PaperGridCube_volume_eq hL_pos cell (0, 0, 0)
        rw [h1]
        have h2 : volume (wz1PaperGridCube L (0, 0, 0)) = ENNReal.ofReal (L ^ 3) :=
          wz1PaperGridCube_volume_exact hL_pos
        rw [h2]
        have h4 : Kakeya.realRpowENN L 3 = ENNReal.ofReal (L ^ 3) := by
          simp [Kakeya.realRpowENN, Real.rpow_natCast] <;> rfl
        exact h4.symm
      calc
        volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau)
          ≥ volume cube := measure_mono h_cube_sub
        _ = Kakeya.realRpowENN L 3 := h_volume_cube
    calc
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau
        ≤ Kakeya.realRpowENN L 3 := h_cell_full
      _ ≤ volume (coarseShading.carrier j ∩ S ∩ Metric.closedBall p tau) := h5
  let propertyThree : WZ1PaperTubeShading coarse := propertyOne
  have h_transverse : ∀ p ∈ propertyThree.union,
      ∀ (i : Fin coarse.card),
        p ∈ propertyThree.carrier i →
          ∃ (j : Fin coarse.card),
            p ∈ propertyOne.carrier j ∧
              Real.rpow L epsilon₃ ≤
                ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ := by
    intro p hp i hi
    have h_p_in_S : p ∈ S := by rw [h_union_eq] at hp; exact hp
    have h_mult : m ≤ propertyOne.pointMultiplicity p := h_pointwise p hp
    have h_close_lt :
        (paperCloseDirectionCount coarseShading p i kappa : ENNReal) <
          (m : ENNReal) :=
      h_close_count p (by
        rcases (show p ∈ propertyOne.union by
          simpa [propertyThree] using hp) with ⟨j, hj⟩
        exact ⟨j, h_propertyOne_sub j hj⟩)
        i (by simpa [propertyThree] using h_propertyOne_sub i hi)
    rcases paperTransverseFromCloseCountLtMultiplicity
        p hp h_mult h_propertyOne_sub i kappa h_close_lt with ⟨j, hj1, hj2⟩
    refine ⟨j, hj1, ?_⟩
    have h7 : Real.rpow L epsilon₃ ≤ kappa := h_kappa
    have h8 : kappa ≤ ‖wz1Cross (coarse.tube i).direction (coarse.tube j).direction‖ := hj2
    exact h7.trans h8
  exact
    { propertyOne := propertyOne
      propertyOne_sub := h_propertyOne_sub
      propertyOne_mass := h_propertyOne_mass
      propertyThree := propertyThree
      propertyThree_sub := by
        intro i
        exact Set.Subset.refl _
      propertyThree_common_spatial := by
        intro i
        change coarseShading.carrier i ∩ S =
          coarseShading.carrier i ∩ propertyOne.union
        rw [h_union_eq]
      propertyThree_mass := h_propertyOne_mass
      propertyThree_cubical :=
        paperHighMultiplicityRestriction_cubical coarseExtremal.cubical
      multiplicity := m
      multiplicity_pos := hm_pos
      multiplicity_lower_pointwise := h_pointwise
      multiplicity_gt_packing := hm_gt_packing
      propertyOne_full := h_full
      transverse := h_transverse }

/-- Version with a non-strict explicit close-count bound and a separate
multiplicity margin. -/
def pureWz2_propertyP_refinement_general_of_close_count
    {sigma outputLoss L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss coarse coarseShading)
    (h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i))
    (epsilon₁ epsilon₃ : ℝ)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_large : L * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (K : ℕ)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * L ≤ 1 / 2)
    (h_close_count : ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (i : Fin coarse.card),
        p ∈ coarseShading.carrier i →
          (paperCloseDirectionCount coarseShading p i ((K : ℝ) * L) :
              ENNReal) ≤
            ((1600 * K + 1)^5 : ENNReal))
    (m : ℕ)
    (hm_pos : 0 < m)
    (hm_gt_packing :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (hm_gt_general :
      ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal))
    (h_mass_ne_top : coarseShading.mass ≠ ⊤)
    (h_volume_ne_top : volume coarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass)
    (h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L)
    (h_cell_full :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
      Kakeya.realRpowENN L 3) :
    PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) :=
  pureWz2_propertyP_refinement_general_of_close_count_lt
    coarseExtremal h_line epsilon₁ epsilon₃ heps₁_pos heps₃_pos heps_sum
    hL_pos hL_small htau_pos hL_le_tau htau_large htau_sq htau_le_one
    K hK_one hKL_small m
    (fun p hp i hi => (h_close_count p hp i hi).trans_lt hm_gt_general)
    hm_pos hm_gt_packing h_mass_ne_top h_volume_ne_top h_avg h_kappa
    h_cell_full

/-- Backwards-compatible wrapper deriving the close-count premise from the
historical full-line essential-distinctness hypothesis. -/
def pureWz2_propertyP_refinement_general_of_distinctness
    {sigma outputLoss L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss coarse coarseShading)
    (h_essentially_distinct : WZ1PaperIsEssentiallyDistinct coarse)
    (h_line : ∀ i, WZ1PaperTubeInLineClass (coarse.tube i))
    (epsilon₁ epsilon₃ : ℝ)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 10000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_large : L * Real.sqrt 3 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (K : ℕ)
    (hK_one : 1 ≤ K)
    (hKL_small : (K : ℝ) * L ≤ 1 / 2)
    (m : ℕ)
    (hm_pos : 0 < m)
    (hm_gt_packing :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (hm_gt_general :
      ((1600 * K + 1)^5 : ENNReal) < (m : ENNReal))
    (h_mass_ne_top : coarseShading.mass ≠ ⊤)
    (h_volume_ne_top : volume coarseShading.union ≠ ⊤)
    (h_avg : (m : ENNReal) * volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass)
    (h_kappa : Real.rpow L epsilon₃ ≤ (K : ℝ) * L)
    (h_cell_full :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
      Kakeya.realRpowENN L 3) :
    PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau) :=
  pureWz2_propertyP_refinement_general_of_close_count
    coarseExtremal h_line epsilon₁ epsilon₃ heps₁_pos heps₃_pos heps_sum
    hL_pos hL_small htau_pos hL_le_tau htau_large htau_sq htau_le_one
    K hK_one hKL_small
    (pureWz2_close_direction_count_general (delta := (0 : ℝ))
      (sigma := sigma) (L := L) (K := K) h_essentially_distinct h_line
      hL_pos hL_small hK_one hKL_small)
    m hm_pos hm_gt_packing hm_gt_general h_mass_ne_top h_volume_ne_top
    h_avg h_kappa h_cell_full

/-!
## Adapted Córdoba L² slab lower bound

Takes `PureWZ2PropertyPData` and produces the slab volume lower bound:
  volume(propertyOne ∩ ball(q, 3τ) ∩ slab(width W)) ≥
    L^(1 + 7ε₁ + ε₃) * τ² / 200

This is the key to the 1-σ exponent.
-/

/-!
## Local volume upper bound

Simple cell counting using the balanced cover.
-/

/--
Local volume upper bound via balanced cover cell counting.

TODO: prove using grid geometry and `balanced.fine_cell_mass`.
-/
theorem pureWz2_local_volume_upper
    {delta sigma L tau : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hL_pos : 0 < L) (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (q : Point3) :
    volume (fineShading.union ∩ Metric.closedBall q tau) ≤
      (8 * 27 : ENNReal) * ENNReal.ofReal ((tau / L) ^ 3) * balanced.cellMass := by
  -- Step 1: fine union ⊆ coarse union via point_compatibility
  have h_fine_sub_coarse : fineShading.union ⊆ coarseShading.union := by
    intro p hp
    rcases hp with ⟨source, hsource⟩
    rcases cover.covers source with ⟨parent, hcovers⟩
    exact ⟨parent, balanced.point_compatibility source parent hcovers p hsource⟩

  -- Step 2: Define intersecting active cells
  let intersecting : Finset (ℤ × ℤ × ℤ) :=
    balanced.activeCells.filter fun cell =>
      (wz1PaperGridCube L cell ∩ Metric.closedBall q tau).Nonempty

  -- Step 3: fine union ∩ ball ⊆ union over intersecting cells
  have h3 : fineShading.union ∩ Metric.closedBall q tau ⊆
      ⋃ cell ∈ intersecting, (fineShading.union ∩ wz1PaperGridCube L cell) := by
    intro p hp
    have hp_fine : p ∈ fineShading.union := hp.1
    have hp_ball : p ∈ Metric.closedBall q tau := hp.2
    have hp_coarse : p ∈ coarseShading.union := h_fine_sub_coarse hp_fine
    rw [balanced.coarse_union_eq] at hp_coarse
    rcases Set.mem_iUnion₂.mp hp_coarse with ⟨cell, hcell, hpcube⟩
    have h_nonempty : (wz1PaperGridCube L cell ∩ Metric.closedBall q tau).Nonempty :=
      ⟨p, hpcube, hp_ball⟩
    have h_inter : cell ∈ intersecting := by
      simp only [intersecting, Finset.mem_filter] <;> exact ⟨hcell, h_nonempty⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, h_inter, ⟨hp_fine, hpcube⟩⟩

  -- Step 4: Volume ≤ sum over intersecting cells
  have h4 : volume (fineShading.union ∩ Metric.closedBall q tau) ≤
      ∑ cell ∈ intersecting, volume (fineShading.union ∩ wz1PaperGridCube L cell) := by
    calc
      volume (fineShading.union ∩ Metric.closedBall q tau)
        ≤ volume (⋃ cell ∈ intersecting, (fineShading.union ∩ wz1PaperGridCube L cell)) :=
          measure_mono h3
      _ ≤ ∑ cell ∈ intersecting, volume (fineShading.union ∩ wz1PaperGridCube L cell) := by
          exact MeasureTheory.measure_biUnion_finset_le intersecting _

  -- Step 5: Each active cell has fine mass cellMass
  have h5 : ∀ cell ∈ intersecting,
      volume (fineShading.union ∩ wz1PaperGridCube L cell) = balanced.cellMass := by
    intro cell hcell
    have h_active : cell ∈ balanced.activeCells := (Finset.mem_filter.mp hcell).1
    exact balanced.fine_cell_mass cell h_active

  have h_sum : ∑ cell ∈ intersecting, volume (fineShading.union ∩ wz1PaperGridCube L cell) =
      (intersecting.card : ENNReal) * balanced.cellMass := by
    rw [Finset.sum_congr rfl h5]
    simp [Finset.sum_const]
    <;> ring

  have h_main : volume (fineShading.union ∩ Metric.closedBall q tau) ≤
      (intersecting.card : ENNReal) * balanced.cellMass := by
    calc
      volume (fineShading.union ∩ Metric.closedBall q tau)
        ≤ ∑ cell ∈ intersecting, volume (fineShading.union ∩ wz1PaperGridCube L cell) := h4
      _ = (intersecting.card : ENNReal) * balanced.cellMass := h_sum

  -- Step 6: Bound cardinality of intersecting cells
  let boundI (i : Fin 3) : Finset ℤ :=
    Finset.Icc (Int.floor ((q i - tau) / L) - 1) (Int.ceil ((q i + tau) / L))
  let boundSet : Finset (ℤ × ℤ × ℤ) :=
    boundI 0 ×ˢ boundI 1 ×ˢ boundI 2

  have h_card_bound : ∀ (i : Fin 3), ((boundI i).card : ℝ) ≤ 6 * tau / L := by
    intro i
    set x : ℝ := (q i - tau) / L with hx
    set y : ℝ := (q i + tau) / L with hy
    set a : ℤ := Int.floor x - 1 with ha
    set b : ℤ := Int.ceil y with hb
    have h_diff : y - x = 2 * tau / L := by
      dsimp only [x, y] <;> ring
    have hxy : x ≤ y := by
      have h : 0 ≤ y - x := by rw [h_diff] <;> positivity
      linarith
    have h_ab : a ≤ b := by
      have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      have h2 : y ≤ (Int.ceil y : ℝ) := Int.le_ceil y
      have h3 : (Int.floor x : ℝ) ≤ (Int.ceil y : ℝ) := by linarith
      have h4 : Int.floor x ≤ Int.ceil y := by exact_mod_cast h3
      simp only [ha, hb] at * <;> omega
    have h_boundI_eq : boundI i = Finset.Icc a b := by
      simp [boundI, ha, hb, hx, hy] <;> rfl
    have h_card : (boundI i).card = (b + 1 - a).toNat := by
      rw [h_boundI_eq]
      exact Int.card_Icc a b
    have h_pos : 0 ≤ b + 1 - a := by omega
    have h9 : ((b + 1 - a).toNat : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      have h10 : (b + 1 - a).toNat = b + 1 - a := Int.toNat_of_nonneg h_pos
      have h11 : ((b + 1 - a).toNat : ℝ) = ↑(b + 1 - a) := by exact_mod_cast h10
      rw [h11]
      <;> simp [Int.cast_add, Int.cast_sub, Int.cast_one] <;> ring
    have h_main : ((boundI i).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      rw [h_card, h9]
    have h_b : (b : ℝ) < y + 1 := by
      simp only [hb]
      exact Int.ceil_lt_add_one y
    have h_a : (a : ℝ) ≥ x - 2 := by
      have h4 : x - 1 < (Int.floor x : ℝ) := Int.sub_one_lt_floor x
      have h5 : (a : ℝ) = (Int.floor x : ℝ) - 1 := by
        simp [ha, Int.cast_sub, Int.cast_one] <;> ring
      rw [h5]
      linarith
    have h_ub : (b : ℝ) + 1 - (a : ℝ) ≤ y - x + 4 := by linarith
    have h7 : 1 ≤ tau / L := by
      calc 1 = L / L := by field_simp [hL_pos.ne'] <;> ring
        _ ≤ tau / L := by gcongr
    have h6 : 4 ≤ 4 * tau / L := by
      calc 4 = 4 * (1 : ℝ) := by ring
        _ ≤ 4 * (tau / L) := by gcongr <;> exact h7
        _ = 4 * tau / L := by ring
    have h5 : 2 * tau / L + 4 ≤ 6 * tau / L := by
      have h : 4 ≤ 4 * tau / L := h6
      have h' : 2 * tau / L + 4 ≤ 2 * tau / L + 4 * tau / L := by
        gcongr
        <;> exact h
      have h'' : 2 * tau / L + 4 * tau / L = 6 * tau / L := by ring
      rw [h''] at h'
      exact h'
    rw [h_main]
    have h_final : (b : ℝ) + 1 - (a : ℝ) ≤ 6 * tau / L := by
      calc
        (b : ℝ) + 1 - (a : ℝ) ≤ y - x + 4 := h_ub
        _ = 2 * tau / L + 4 := by rw [h_diff] <;> ring
        _ ≤ 6 * tau / L := h5
    exact h_final

  have h_coord_lemma : ∀ (p : Point3), p ∈ Metric.closedBall q tau →
      ∀ (cell : ℤ × ℤ × ℤ), gridIndex L p = cell → cell ∈ boundSet := by
    intro p hpball cell hgrid
    have hball : ‖p - q‖ ≤ tau := by
      have h : dist p q ≤ tau := by simpa [Metric.mem_closedBall] using hpball
      simpa [dist_eq_norm] using h
    have hcoord : ∀ i : Fin 3, |p i - q i| ≤ tau := by
      intro i
      have h : |p i - q i| ≤ ‖p - q‖ := by
        have h' : |(p - q) i| ≤ ‖p - q‖ := by
          have h1 : ((p - q) i)^2 ≤ ∑ j : Fin 3, ((p - q) j)^2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          have h2 : ‖p - q‖^2 = ∑ j : Fin 3, ((p - q) j)^2 := by
            have h21 : ‖p - q‖ = Real.sqrt (∑ j : Fin 3, ((p - q) j)^2) := by
              simpa [EuclideanSpace.norm_eq] using rfl
            rw [h21]
            have hpos : 0 ≤ ∑ j : Fin 3, ((p - q) j)^2 := by positivity
            rw [Real.sq_sqrt hpos]
          have h3 : |(p - q) i|^2 ≤ ‖p - q‖^2 := by
            have h4 : |(p - q) i|^2 = ((p - q) i)^2 := by simp [sq_abs]
            rw [h4, h2]; exact h1
          have h5 : 0 ≤ |(p - q) i| := by positivity
          have h6 : 0 ≤ ‖p - q‖ := by positivity
          nlinarith
        simpa using h'
      exact h.trans hball
    have hg0 : (gridIndex L p).1 = cell.1 := by rw [hgrid]
    have hg1 : (gridIndex L p).2.1 = cell.2.1 := by rw [hgrid]
    have hg2 : (gridIndex L p).2.2 = cell.2.2 := by rw [hgrid]
    have h0 : cell.1 = Int.floor (p 0 / L) := by simpa [gridIndex] using hg0.symm
    have h1 : cell.2.1 = Int.floor (p 1 / L) := by simpa [gridIndex] using hg1.symm
    have h2 : cell.2.2 = Int.floor (p 2 / L) := by simpa [gridIndex] using hg2.symm
    have h_bound : ∀ (k : ℤ) (i : Fin 3), (k : ℝ) = Int.floor (p i / L) → k ∈ boundI i := by
      intro k i hk
      simp only [boundI, Finset.mem_Icc]
      constructor
      · have h6 : (k : ℝ) ≥ (q i - tau) / L - 1 := by
          rw [hk]
          have h8 : (Int.floor (p i / L) : ℝ) > (p i / L) - 1 := Int.sub_one_lt_floor (p i / L)
          have h9 : p i ≥ q i - tau := by linarith [abs_le.mp (hcoord i)]
          have h10 : p i / L ≥ (q i - tau) / L := by gcongr
          linarith
        have h_floor_le : (Int.floor ((q i - tau) / L) : ℝ) ≤ (q i - tau) / L := Int.floor_le _
        have h_lower' : (Int.floor ((q i - tau) / L) - 1 : ℝ) ≤ (k : ℝ) := by linarith
        exact_mod_cast h_lower'
      · have h6 : (k : ℝ) ≤ (q i + tau) / L := by
          rw [hk]
          have h8 : (Int.floor (p i / L) : ℝ) ≤ p i / L := Int.floor_le _
          have h9 : p i ≤ q i + tau := by linarith [abs_le.mp (hcoord i)]
          have h10 : p i / L ≤ (q i + tau) / L := by gcongr
          linarith
        have h_ceil_le : (q i + tau) / L ≤ (Int.ceil ((q i + tau) / L) : ℝ) := Int.le_ceil _
        have h_upper' : (k : ℝ) ≤ (Int.ceil ((q i + tau) / L) : ℝ) := by linarith
        exact_mod_cast h_upper'
    have h0' : (cell.1 : ℝ) = Int.floor (p 0 / L) := by exact_mod_cast h0
    have h1' : (cell.2.1 : ℝ) = Int.floor (p 1 / L) := by exact_mod_cast h1
    have h2' : (cell.2.2 : ℝ) = Int.floor (p 2 / L) := by exact_mod_cast h2
    have hmb0 : cell.1 ∈ boundI 0 := h_bound cell.1 0 h0'
    have hmb1 : cell.2.1 ∈ boundI 1 := h_bound cell.2.1 1 h1'
    have hmb2 : cell.2.2 ∈ boundI 2 := h_bound cell.2.2 2 h2'
    simp only [boundSet, Finset.mem_product] <;> exact ⟨hmb0, hmb1, hmb2⟩

  have h_sub : intersecting ⊆ boundSet := by
    intro cell hcell
    have h_nonempty := (Finset.mem_filter.mp hcell).2
    rcases h_nonempty with ⟨p, hpcube, hpball⟩
    have hgrid : gridIndex L p = cell := by
      simpa [wz1PaperGridCube] using hpcube
    exact h_coord_lemma p hpball cell hgrid

  have h9 : intersecting.card ≤ boundSet.card := Finset.card_le_card h_sub
  have h10 : (boundSet.card : ℝ) =
      ((boundI 0).card : ℝ) * ((boundI 1).card : ℝ) * ((boundI 2).card : ℝ) := by
    simp [boundSet, Finset.card_product] <;> norm_cast <;> ring
  have h11 : ((boundI 0).card : ℝ) * ((boundI 1).card : ℝ) * ((boundI 2).card : ℝ) ≤
      (6 * tau / L) ^ 3 := by
    have h12 := h_card_bound 0
    have h13 := h_card_bound 1
    have h14 := h_card_bound 2
    have h_pos1 : 0 ≤ ((boundI 0).card : ℝ) := by positivity
    have h_pos2 : 0 ≤ ((boundI 1).card : ℝ) := by positivity
    have h15 : ((boundI 0).card : ℝ) * ((boundI 1).card : ℝ) ≤ (6 * tau / L) * (6 * tau / L) := by
      exact mul_le_mul h12 h13 h_pos2 (by positivity)
    have h16 : ((boundI 0).card : ℝ) * ((boundI 1).card : ℝ) * ((boundI 2).card : ℝ) ≤
        ((6 * tau / L) * (6 * tau / L)) * ((boundI 2).card : ℝ) := by
      exact mul_le_mul_of_nonneg_right h15 (by positivity)
    have h17 : ((6 * tau / L) * (6 * tau / L)) * ((boundI 2).card : ℝ) ≤
        (6 * tau / L) * (6 * tau / L) * (6 * tau / L) := by
      exact mul_le_mul_of_nonneg_left h14 (by positivity)
    have h18 : (6 * tau / L) * (6 * tau / L) * (6 * tau / L) = (6 * tau / L) ^ 3 := by ring
    calc
      _ ≤ ((6 * tau / L) * (6 * tau / L)) * ((boundI 2).card : ℝ) := h16
      _ ≤ (6 * tau / L) * (6 * tau / L) * (6 * tau / L) := h17
      _ = (6 * tau / L) ^ 3 := h18
  have h_card : (intersecting.card : ℝ) ≤ (8 * 27 : ℝ) * (tau / L) ^ 3 := by
    calc
      (intersecting.card : ℝ)
        ≤ (boundSet.card : ℝ) := by exact_mod_cast h9
      _ = ((boundI 0).card : ℝ) * ((boundI 1).card : ℝ) * ((boundI 2).card : ℝ) := h10
      _ ≤ (6 * tau / L) ^ 3 := h11
      _ = (8 * 27 : ℝ) * (tau / L) ^ 3 := by ring

  have h16 : (intersecting.card : ENNReal) ≤
      ENNReal.ofReal ((8 * 27 : ℝ) * (tau / L) ^ 3) := by
    have h1 : (intersecting.card : ENNReal) = ENNReal.ofReal (intersecting.card : ℝ) := by simp
    rw [h1]
    exact ENNReal.ofReal_le_ofReal h_card

  -- Step 7: Combine
  have h17 : (8 * 27 : ENNReal) * ENNReal.ofReal ((tau / L) ^ 3) =
      ENNReal.ofReal ((8 * 27 : ℝ) * (tau / L) ^ 3) := by
    have h21 : (8 * 27 : ENNReal) = ENNReal.ofReal (8 * 27 : ℝ) := by norm_cast
    rw [h21]
    have h22 : ENNReal.ofReal (8 * 27 : ℝ) * ENNReal.ofReal ((tau / L) ^ 3) =
        ENNReal.ofReal ((8 * 27 : ℝ) * (tau / L) ^ 3) := by
      have h_pos1 : 0 ≤ (8 * 27 : ℝ) := by positivity
      have h' : ∀ (y : ℝ), ENNReal.ofReal ((8 * 27 : ℝ) * y) =
          ENNReal.ofReal (8 * 27 : ℝ) * ENNReal.ofReal y := by
        intro y
        exact ENNReal.ofReal_mul h_pos1
      exact (h' ((tau / L) ^ 3)).symm
    exact h22
  have h_final : (intersecting.card : ENNReal) * balanced.cellMass ≤
      (8 * 27 : ENNReal) * ENNReal.ofReal ((tau / L) ^ 3) * balanced.cellMass := by
    calc
      (intersecting.card : ENNReal) * balanced.cellMass
        ≤ ENNReal.ofReal ((8 * 27 : ℝ) * (tau / L) ^ 3) * balanced.cellMass :=
          mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = (8 * 27 : ENNReal) * ENNReal.ofReal ((tau / L) ^ 3) * balanced.cellMass := by
        rw [h17] <;> ring
  exact h_main.trans h_final

/-!
## Main local AD theorem

Constructs the every-scale local AD bound.

The proof uses the nearby-scale CWA to obtain balanced-cover data at each
requested scale, then applies the property-(P) refinement and Córdoba L²
argument to obtain the 1-σ covering bound.
-/

/--
Packaged data for the HIGH case of the local AD dichotomy.

Provides everything needed to apply `slab_to_ad`: a unit direction `v`,
a measurable ambient set `S` containing the target ball, slab volume bounds,
and the arithmetic condition ensuring the covering bound fits the AD constant.
-/
structure PureWZ2LocalADHighData
    {delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (C : ENNReal)
    (rho : ℝ)
    (q : Point3)
    (hq : q ∈ shading.union) where
  v : Point3
  hv_unit : ‖v‖ = 1
  S : Set Point3
  hS_meas : MeasurableSet S
  W : ℝ
  V_min : ℝ
  V_total : ℝ
  hW_pos : 0 < W
  hVmin_pos : 0 < V_min
  hV_total_pos : 0 < V_total
  hV_total : volume S ≤ ENNReal.ofReal V_total
  h_slab : ∀ t ∈ scalarProjection v S,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ W}) ≥ ENNReal.ofReal V_min
  h_arithmetic : ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) ≤ C
  h_dir : v = planeMap ⟨q, hq⟩
  h_contain : shading.union ∩ Metric.closedBall q (Real.sqrt rho) ⊆ S

/--
Dichotomy for the local AD assembly.

For each scale `rho` and point `q`, either:
- HIGH: there is packaged slab/AD data proving the 1-σ bound, OR
- LOW: the shaded union near `q` has small volume.
-/
structure PureWZ2LocalADDichotomy
    {delta' sigma loss_src : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (C : ENNReal) where
  decide : ∀ (rho : ℝ) (hrho : delta' ≤ rho) (q : Point3) (hq : q ∈ shading.union),
    Nonempty (PureWZ2LocalADHighData planeMap C rho q hq) ∨
    (volume (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ≤
       C * Kakeya.realRpowENN rho (1 - sigma))

/-!
## Slab-to-AD conversion lemma

Converts Córdoba slab volume lower bounds into `PureWZ2PaperADSet1` covering
bounds via the finite covering lemma.
-/

/-- Convert Córdoba slab volume bounds to a 1-σ AD covering bound.

Given a measurable set `S`, a unit direction `v`, slab width `W`,
slab volume lower bound `V_min`, and total volume upper bound `V_total`,
if `(V_total / V_min) * (2 * W / rho + 2) ≤ C`, then the scalar
projection of `S` in direction `v` has AD exponent `1 - sigma` at scale `rho`
with constant `C`. -/
lemma slab_to_ad
    {sigma rho : ℝ}
    {C : ENNReal}
    {S : Set Point3}
    {v : Point3}
    (hv_unit : ‖v‖ = 1)
    (hS_meas : MeasurableSet S)
    (W V_min V_total : ℝ)
    (hW_pos : 0 < W)
    (hVmin_pos : 0 < V_min)
    (hV_total_pos : 0 < V_total)
    (hV_total : volume S ≤ ENNReal.ofReal V_total)
    (h_slab : ∀ t ∈ scalarProjection v S,
        volume (S ∩ {x | |inner ℝ x v - t| ≤ W}) ≥ ENNReal.ofReal V_min)
    (hrho_pos : 0 < rho)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hC_one : (1 : ENNReal) ≤ C)
    (hC_top : C ≠ ⊤)
    (h_arithmetic :
        ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) ≤ C) :
    PureWZ2PaperADSet1 (scalarProjection v S) rho (1 - sigma) C := by
  have halpha_pos : 0 < 1 - sigma := by linarith
  have halpha_le_one : (1 - sigma) ≤ 1 := by linarith
  let proj : Point3 → ℝ := fun x => inner ℝ x v
  have hproj_meas : Measurable proj := by
    fun_prop
  have h_disjoint : ∀ (t t' : ℝ), |t - t'| > 2 * W →
      Disjoint {x : Point3 | |proj x - t| ≤ W} {x : Point3 | |proj x - t'| ≤ W} := by
    intro t t' h
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : |proj x - t| ≤ W := hx1
    have h2 : |proj x - t'| ≤ W := hx2
    have h3 : |t - t'| ≤ |proj x - t| + |proj x - t'| := by
      have h4 : t - t' = (proj x - t') - (proj x - t) := by ring
      rw [h4]
      have h5 : |(proj x - t') - (proj x - t)| ≤ |proj x - t'| + |proj x - t| :=
        abs_sub _ _
      linarith
    have h6 : |t - t'| ≤ 2 * W := by linarith
    linarith
  refine' ⟨by linarith, by linarith, by linarith, hC_one, hC_top, _⟩
  intro rho' hrho' hrho_ge left length hlength
  have hrho'_pos : 0 < rho' := lt_of_lt_of_le hrho_pos hrho_ge
  let E : Set ℝ := scalarProjection v S ∩ Set.Icc left (left + length)
  have hE_sub : E ⊆ scalarProjection v S := by
    intro x hx
    exact hx.1
  have hE_sub_proj : E ⊆ proj '' S := by
    simpa [scalarProjection] using hE_sub
  have h_slab' : ∀ t ∈ E,
      volume (S ∩ {x | |proj x - t| ≤ W}) ≥ ENNReal.ofReal V_min := by
    intro t ht
    exact h_slab t (hE_sub ht)
  have h_cover := covering_number_from_slab_volumes_subset
    (rho := rho') proj hrho'_pos hW_pos hVmin_pos hS_meas hproj_meas hE_sub_proj h_slab' hV_total h_disjoint
  have h_bound : (↑(Metric.externalCoveringNumber (Real.toNNReal rho') E) : ENNReal) ≤
      ENNReal.ofReal ((V_total / V_min) * (2 * W / rho' + 2)) := h_cover
  have h1 : 2 * W / rho' ≤ 2 * W / rho := by
    apply div_le_div_of_nonneg_left
    · positivity
    · linarith
    · linarith
  have h_monotone : (V_total / V_min) * (2 * W / rho' + 2) ≤
      (V_total / V_min) * (2 * W / rho + 2) := by
    gcongr
    <;> linarith
  have h_bound2 : (↑(Metric.externalCoveringNumber (Real.toNNReal rho') E) : ENNReal) ≤
      ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) :=
    h_bound.trans (ENNReal.ofReal_le_ofReal h_monotone)
  have hlength_pos : 0 < length := by linarith [hrho'_pos, hlength]
  have h_bound3 : (↑(Metric.externalCoveringNumber (Real.toNNReal rho') E) : ENNReal) ≤ C :=
    h_bound2.trans h_arithmetic
  have h_ratio_pos : 0 < length / rho' := by positivity
  have h_ratio_one : 1 ≤ length / rho' := by
    calc 1 = rho' / rho' := by field_simp [hrho'_pos.ne']
      _ ≤ length / rho' := by gcongr
  have h_rpow_one : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho') (1 - sigma) := by
    have h7 : 1 ≤ length / rho' := h_ratio_one
    have h8 : 0 ≤ (1 - sigma) := by linarith
    have h9 : (1 : ℝ) ≤ Real.rpow (length / rho') (1 - sigma) := by
      apply Real.one_le_rpow
      <;> linarith
    have h10 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h10]
    exact ENNReal.ofReal_le_ofReal h9
  have h_final : C ≤ C * Kakeya.realRpowENN (length / rho') (1 - sigma) := by
    exact le_mul_of_one_le_right' h_rpow_one
  have h_goal : (↑(Metric.externalCoveringNumber (Real.toNNReal rho') E) : ENNReal) ≤
      C * Kakeya.realRpowENN (length / rho') (1 - sigma) :=
    h_bound3.trans h_final
  have h_nnreal_eq : (⟨rho', hrho'⟩ : NNReal) = Real.toNNReal rho' := by
    rw [Real.toNNReal_of_nonneg hrho'] <;> rfl
  simpa [E, h_nnreal_eq] using h_goal

/-- Simplify the HIGH-case arithmetic condition under standard parameter choices.

Given Córdoba slab data with `L = rho`, `tau^2 = 4*L`, slab width `W = 40*L`,
and slab volume lower bound
`V_min = L^(1+7*epsilon_1+epsilon_3) * tau^2 / 200`,
the `slab_to_ad` arithmetic condition
`(V_total / V_min) * (2*W/rho + 2) ≤ delta'^(-loss_src)`
reduces to
`4100 * V_total ≤ rho^(2+7*epsilon_1+epsilon_3) * delta'^(-loss_src)`.

This directly supplies the `h_arithmetic` field of `PureWZ2LocalADHighData`.
-/
lemma high_case_arithmetic_reduction
    {delta' loss_src rho L tau V_total epsilon₁ epsilon₃ : ℝ}
    (hdelta'_pos : 0 < delta')
    (hrho_pos : 0 < rho)
    (hL_pos : 0 < L)
    (htau_pos : 0 < tau)
    (hV_total_pos : 0 < V_total)
    (hL_eq_rho : L = rho)
    (htau_sq : tau ^ 2 = 4 * L)
    (h_main : 4100 * V_total ≤
        Real.rpow rho (2 + 7 * epsilon₁ + epsilon₃) * Real.rpow delta' (-loss_src)) :
    ENNReal.ofReal ((V_total / (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
      (2 * (40 * L) / rho + 2)) ≤ Kakeya.realRpowENN delta' (-loss_src) := by
  set R : ℝ := Real.rpow rho (2 + 7 * epsilon₁ + epsilon₃) with hR_def
  have hR_pos : 0 < R := Real.rpow_pos_of_pos hrho_pos _
  have hVmin_simp : Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200 = R / 50 := by
    have htau_sq_rho : tau ^ 2 = 4 * rho := by
      calc tau ^ 2 = 4 * L := htau_sq
        _ = 4 * rho := by rw [hL_eq_rho]
    rw [hL_eq_rho, htau_sq_rho]
    have h_exp : Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * rho = R := by
      have h1 : Real.rpow rho ((1 + 7 * epsilon₁ + epsilon₃) + 1) =
          Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * Real.rpow rho 1 :=
        Real.rpow_add hrho_pos _ _
      have h2 : Real.rpow rho 1 = rho := by simp
      have h3 : (1 + 7 * epsilon₁ + epsilon₃) + (1 : ℝ) = 2 + 7 * epsilon₁ + epsilon₃ := by ring
      rw [h3] at h1
      rw [h2] at h1
      exact h1.symm
    have h4 : Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * (4 * rho) / 200 =
        Real.rpow rho (1 + 7 * epsilon₁ + epsilon₃) * rho / 50 := by ring
    rw [h4, h_exp]
  have hW_simp : 2 * (40 * L) / rho + 2 = 82 := by
    rw [hL_eq_rho]
    field_simp [hrho_pos.ne'] <;> ring
  have h_expr_simp : (V_total / (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
      (2 * (40 * L) / rho + 2) = 4100 * V_total / R := by
    rw [hVmin_simp, hW_simp]
    field_simp [hR_pos.ne'] <;> ring
  have h_real : 4100 * V_total / R ≤ Real.rpow delta' (-loss_src) := by
    calc 4100 * V_total / R
      _ ≤ (R * Real.rpow delta' (-loss_src)) / R := by gcongr
      _ = Real.rpow delta' (-loss_src) := by
        field_simp [hR_pos.ne'] <;> ring
  have h_final : (V_total / (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
      (2 * (40 * L) / rho + 2) ≤ Real.rpow delta' (-loss_src) := by
    rw [h_expr_simp]
    exact h_real
  have h_nonneg : 0 ≤ (V_total / (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau ^ 2 / 200)) *
      (2 * (40 * L) / rho + 2) := by
    rw [h_expr_simp]
    positivity
  have h6 : Kakeya.realRpowENN delta' (-loss_src) =
      ENNReal.ofReal (Real.rpow delta' (-loss_src)) := by
    simp [Kakeya.realRpowENN]
  rw [h6]
  exact ENNReal.ofReal_le_ofReal h_final

/-!
## Direct tube-counting AD bound

Alternative to the Córdoba slab approach for the HIGH case.

Uses the CWA + essentially-distinct packing to bound the number of tubes
whose projection falls in an interval, then converts to a covering number.

Works for all σ when `outputLoss < 2 + loss` and δ' is sufficiently small.
-/

/-- Key inequality for short intervals: `L/2 ≤ (L/rho')^(1-σ)` when `L ≤ 2√ρ`. -/
lemma direct_counting_key_short
    {sigma rho rho' : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hrho'_pos : 0 < rho')
    (hrho'_le_one : rho' ≤ 1)
    {L : ℝ}
    (hL1 : rho' ≤ L)
    (hL2 : L ≤ 2 * Real.sqrt rho) :
    (L / 2 : ℝ) ≤ (L / rho') ^ (1 - sigma) := by
  have hL_pos : 0 < L := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le_one
    have h2 : Real.sqrt 1 = 1 := by simp
    linarith
  have hsigma_le_one : sigma ≤ 1 := by linarith
  have h_pos2 : 0 < rho' ^ (1 - sigma) := by positivity
  have h1 : L ^ sigma ≤ (2 : ℝ)^sigma := by
    have h1b : L ^ sigma ≤ (2 * Real.sqrt rho) ^ sigma := Real.rpow_le_rpow (by linarith) hL2 (by linarith)
    have h1c : (2 * Real.sqrt rho) ^ sigma = (2 : ℝ)^sigma * (Real.sqrt rho)^sigma := Real.mul_rpow (by positivity) (by positivity)
    have h1d : (Real.sqrt rho)^sigma ≤ 1 := Real.rpow_le_one hsqrt_nonneg hsqrt_le_one (by linarith)
    calc L ^ sigma ≤ (2 * Real.sqrt rho) ^ sigma := h1b
      _ = (2 : ℝ)^sigma * (Real.sqrt rho)^sigma := h1c
      _ ≤ (2 : ℝ)^sigma * 1 := by gcongr
      _ = (2 : ℝ)^sigma := by ring
  have h2 : rho'^(1 - sigma) ≤ 1 := Real.rpow_le_one (by linarith) hrho'_le_one (by linarith)
  have h3 : L ^ sigma * rho'^(1 - sigma) ≤ 2 := by
    have h4 : (2 : ℝ)^sigma ≤ 2 := by
      have h5 : (2 : ℝ)^sigma ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hsigma_le_one
      have h6 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
      linarith
    calc L ^ sigma * rho'^(1 - sigma) ≤ (2 : ℝ)^sigma * 1 := by gcongr
      _ = (2 : ℝ)^sigma := by ring
      _ ≤ 2 := h4
  have h4 : L ^ sigma * L^(1 - sigma) = L := by
    have h51 : L ^ (sigma + (1 - sigma)) = L ^ sigma * L ^ (1 - sigma) := Real.rpow_add hL_pos sigma (1 - sigma)
    have h52 : sigma + (1 - sigma) = 1 := by ring
    rw [h52] at h51
    have h53 : L ^ (1 : ℝ) = L := by simp
    rw [h53] at h51
    exact h51.symm
  have h5 : L * rho'^(1 - sigma) ≤ 2 * L^(1 - sigma) := by
    have h61 : L * rho'^(1 - sigma) = (L ^ sigma * rho'^(1 - sigma)) * L^(1 - sigma) := by
      have h_step1 : L * rho'^(1 - sigma) = (L ^ sigma * L^(1 - sigma)) * rho'^(1 - sigma) :=
        congr_arg (fun x => x * rho'^(1 - sigma)) h4.symm
      rw [h_step1]
      ring
    rw [h61]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have h6 : (L / rho') ^ (1 - sigma) = L^(1 - sigma) / rho'^(1 - sigma) := Real.div_rpow (by linarith) (by linarith) (1 - sigma)
  rw [h6]
  have h7 : (L * rho'^(1 - sigma)) / (2 * rho'^(1 - sigma)) = L / 2 := by field_simp [h_pos2.ne']
  have h8 : (2 * L^(1 - sigma)) / (2 * rho'^(1 - sigma)) = L^(1 - sigma) / rho'^(1 - sigma) := by field_simp [h_pos2.ne']
  have h9 : (L * rho'^(1 - sigma)) / (2 * rho'^(1 - sigma)) ≤ (2 * L^(1 - sigma)) / (2 * rho'^(1 - sigma)) := by
    exact div_le_div_of_nonneg_right h5 (by positivity)
  rw [h7, h8] at h9
  exact h9

lemma direct_counting_key_long
    {sigma rho rho' : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hrho'_pos : 0 < rho')
    (hrho'_le_one : rho' ≤ 1)
    {L : ℝ}
    (hL : 2 * Real.sqrt rho < L) :
    Real.sqrt rho ≤ (L / rho') ^ (1 - sigma) := by
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le_one
    have h2 : Real.sqrt 1 = 1 := by simp
    linarith
  have halpha_nonneg : 0 ≤ 1 - sigma := by linarith
  have halpha_le_one : 1 - sigma ≤ 1 := by linarith
  have h1 : (2 * Real.sqrt rho) / rho' ≤ L / rho' := by gcongr
  have h2 : (2 * Real.sqrt rho) / rho' ≥ 2 * Real.sqrt rho := by
    have h3 : 0 < 2 * Real.sqrt rho := by positivity
    calc (2 * Real.sqrt rho) / rho' ≥ (2 * Real.sqrt rho) / 1 := by gcongr
      _ = 2 * Real.sqrt rho := by ring
  have h5 : ((2 * Real.sqrt rho) / rho') ^ (1 - sigma) ≤ (L / rho') ^ (1 - sigma) :=
    Real.rpow_le_rpow (by positivity) h1 halpha_nonneg
  have h6 : (2 * Real.sqrt rho) ^ (1 - sigma) = (2 : ℝ)^(1 - sigma) * (Real.sqrt rho)^(1 - sigma) :=
    Real.mul_rpow (by positivity) (by positivity)
  have h7 : (Real.sqrt rho)^(1 - sigma) ≥ Real.sqrt rho := by
    have h71 : (Real.sqrt rho)^(1 : ℝ) ≤ (Real.sqrt rho)^(1 - sigma) :=
      Real.rpow_le_rpow_of_exponent_ge hsqrt_pos hsqrt_le_one halpha_le_one
    have h72 : (Real.sqrt rho)^(1 : ℝ) = Real.sqrt rho := by simp
    rw [h72] at h71
    exact h71
  have h8 : (2 : ℝ)^(1 - sigma) ≥ 1 := by
    have h81 : (2 : ℝ)^(0 : ℝ) ≤ (2 : ℝ)^(1 - sigma) := Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha_nonneg
    have h82 : (2 : ℝ)^(0 : ℝ) = 1 := by simp
    linarith
  have h9 : (2 : ℝ)^(1 - sigma) * (Real.sqrt rho)^(1 - sigma) ≥ Real.sqrt rho := by
    calc (2 : ℝ)^(1 - sigma) * (Real.sqrt rho)^(1 - sigma)
      ≥ 1 * (Real.sqrt rho)^(1 - sigma) := by gcongr
    _ = (Real.sqrt rho)^(1 - sigma) := by ring
    _ ≥ Real.sqrt rho := h7
  have h10 : (2 * Real.sqrt rho) ^ (1 - sigma) ≥ Real.sqrt rho := by rw [h6]; exact h9
  have h11 : ((2 * Real.sqrt rho) / rho') ^ (1 - sigma) ≥ (2 * Real.sqrt rho) ^ (1 - sigma) :=
    Real.rpow_le_rpow (by positivity) h2 halpha_nonneg
  calc (L / rho') ^ (1 - sigma)
    ≥ ((2 * Real.sqrt rho) / rho') ^ (1 - sigma) := h5
  _ ≥ (2 * Real.sqrt rho) ^ (1 - sigma) := h11
  _ ≥ Real.sqrt rho := h10
lemma direct_counting_to_ad_bound
    {sigma delta' rho outputLoss loss : ℝ}
    {E : Set ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hdelta'_pos : 0 < delta')
    (hrho_pos : 0 < rho)
    (hdelta'_le_rho : delta' ≤ rho)
    (hrho_le_one : rho ≤ 1)
    (C_count : ℝ)
    (hC_count_pos : 0 < C_count)
    (hloss_pos : 0 < loss)
    (hcover : ∀ (rho' : ℝ), rho ≤ rho' → ∀ (left length : ℝ), rho' ≤ length →
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho')
         (E ∩ Set.Icc left (left + length))) : ENNReal) ≤
        ENNReal.ofReal (C_count * length) * Kakeya.realRpowENN delta' (-2 - loss))
    (hE_bounded : ∃ (a : ℝ), E ⊆ Set.Icc a (a + 2 * Real.sqrt rho))
    (h_slack : outputLoss < 2 + loss)
    (h_delta_small1 : C_count * 2 * Real.rpow delta' (outputLoss - 2 - loss) ≤ 1)
    (h_delta_small2 : (2 : ℝ)^(2 * sigma + 1) ≤ Real.rpow delta' (-outputLoss)) :
    PureWZ2PaperADSet1 E rho (1 - sigma) (Kakeya.realRpowENN delta' (-outputLoss)) := by
  rcases hE_bounded with ⟨a, hE_a⟩
  have hdelta'_le_one : delta' ≤ 1 := le_trans hdelta'_le_rho hrho_le_one
  have halpha_pos : 0 < 1 - sigma := by linarith
  have halpha_le_one : (1 - sigma) ≤ 1 := by linarith
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le_one
    have h2 : Real.sqrt 1 = 1 := by simp
    linarith
  have houtputLoss_pos : 0 < outputLoss := by
    by_contra h
    have h' : -outputLoss ≥ 0 := by linarith
    have h3 : Real.rpow delta' (-outputLoss) ≤ 1 :=
      Real.rpow_le_one hdelta'_pos.le hdelta'_le_one h'
    have h4 : (1 : ℝ) < (2 : ℝ)^(2 * sigma + 1) := by
      have h5 : 1 < 2 * sigma + 1 := by linarith
      have h6 : (2 : ℝ)^(1 : ℝ) < (2 : ℝ)^(2 * sigma + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h5
      have h7 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
      linarith
    linarith [h_delta_small2, h3]
  have hC_one : (1 : ENNReal) ≤ Kakeya.realRpowENN delta' (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h2 : 1 ≤ Real.rpow delta' (-outputLoss) := by
      have h3 : Real.rpow delta' (0 : ℝ) ≤ Real.rpow delta' (-outputLoss) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta'_pos hdelta'_le_one (by linarith)
      have h4 : Real.rpow delta' (0 : ℝ) = 1 := by simp
      rw [h4] at h3; exact h3
    exact ENNReal.one_le_ofReal.mpr h2
  have hC_top : Kakeya.realRpowENN delta' (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_exp_pos : 0 < 2 + loss - outputLoss := by linarith
  have h_rpow_pos : 0 < Real.rpow delta' (2 + loss - outputLoss) :=
    Real.rpow_pos_of_pos hdelta'_pos _
  have h_small1 : C_count * 2 ≤ Real.rpow delta' (2 + loss - outputLoss) := by
    have h1 : outputLoss - 2 - loss = -(2 + loss - outputLoss) := by ring
    rw [h1] at h_delta_small1
    have h2 : Real.rpow delta' (-(2 + loss - outputLoss)) = (Real.rpow delta' (2 + loss - outputLoss))⁻¹ :=
      Real.rpow_neg hdelta'_pos.le (2 + loss - outputLoss)
    rw [h2] at h_delta_small1
    have h3 : C_count * 2 * (Real.rpow delta' (2 + loss - outputLoss))⁻¹ ≤ 1 := h_delta_small1
    have h41 : C_count * 2 * (Real.rpow delta' (2 + loss - outputLoss))⁻¹ * Real.rpow delta' (2 + loss - outputLoss) = C_count * 2 := by
      field_simp [h_rpow_pos.ne'] <;> ring
    calc C_count * 2
      = C_count * 2 * (Real.rpow delta' (2 + loss - outputLoss))⁻¹ * Real.rpow delta' (2 + loss - outputLoss) := h41.symm
    _ ≤ 1 * Real.rpow delta' (2 + loss - outputLoss) := by gcongr
    _ = Real.rpow delta' (2 + loss - outputLoss) := by ring
  have h5 : Real.rpow delta' (2 + loss - outputLoss) * Real.rpow delta' (-2 - loss) = Real.rpow delta' (-outputLoss) := by
    have h6 : Real.rpow delta' ((2 + loss - outputLoss) + (-2 - loss)) =
        Real.rpow delta' (2 + loss - outputLoss) * Real.rpow delta' (-2 - loss) :=
      Real.rpow_add hdelta'_pos (2 + loss - outputLoss) (-2 - loss)
    have h7 : (2 + loss - outputLoss) + (-2 - loss) = -outputLoss := by ring
    rw [h7] at h6
    exact h6.symm
  have h_mul_bound : ∀ (L : ℝ), 0 < L →
      C_count * L * Real.rpow delta' (-2 - loss) ≤ (L / 2) * Real.rpow delta' (-outputLoss) := by
    intro L hL
    have h9 : C_count * Real.rpow delta' (-2 - loss) ≤ (1 / 2 : ℝ) * Real.rpow delta' (-outputLoss) := by
      have h_pos_rpow : 0 < Real.rpow delta' (-2 - loss) := Real.rpow_pos_of_pos hdelta'_pos (-2 - loss)
      have h_step : (C_count * 2) * Real.rpow delta' (-2 - loss) ≤ Real.rpow delta' (2 + loss - outputLoss) * Real.rpow delta' (-2 - loss) :=
        mul_le_mul_of_nonneg_right h_small1 h_pos_rpow.le
      calc C_count * Real.rpow delta' (-2 - loss)
        = (C_count * 2) * Real.rpow delta' (-2 - loss) / 2 := by ring
      _ ≤ Real.rpow delta' (2 + loss - outputLoss) * Real.rpow delta' (-2 - loss) / 2 := by
        exact div_le_div_of_nonneg_right h_step (by norm_num)
      _ = Real.rpow delta' (-outputLoss) / 2 := by rw [h5] <;> ring
      _ = (1 / 2 : ℝ) * Real.rpow delta' (-outputLoss) := by ring
    calc C_count * L * Real.rpow delta' (-2 - loss)
      = L * (C_count * Real.rpow delta' (-2 - loss)) := by ring
    _ ≤ L * ((1 / 2 : ℝ) * Real.rpow delta' (-outputLoss)) := by gcongr
    _ = (L / 2) * Real.rpow delta' (-outputLoss) := by ring
  have h_rpow_nonneg : 0 ≤ Real.rpow delta' (-outputLoss) := Real.rpow_nonneg hdelta'_pos.le (-outputLoss)
  refine' ⟨hrho_pos, halpha_pos, halpha_le_one, hC_one, hC_top, _⟩
  intro rho' hrho'_nonneg hrho'_ge left length hlength
  have hrho'_pos : 0 < rho' := by linarith
  have hlength_pos : 0 < length := by linarith
  let E_int := E ∩ Set.Icc left (left + length)
  let ε : NNReal := ⟨rho', hrho'_nonneg⟩
  have hε_toNN : Real.toNNReal rho' = ε := by
    apply NNReal.coe_injective
    have h1 : (Real.toNNReal rho' : ℝ) = rho' := Real.coe_toNNReal rho' hrho'_nonneg
    have h2 : (ε : ℝ) = rho' := by
      have hε_def : ε = ⟨rho', hrho'_nonneg⟩ := by rfl
      rw [hε_def]
      <;> rfl
    rw [h1, h2]
  by_cases h_one_ball : rho' > Real.sqrt rho
  · -- One ball suffices
    let c := a + Real.sqrt rho
    have hE_int_sub : E_int ⊆ Metric.closedBall c rho' := by
      intro x hx
      have hxE : x ∈ E := hx.1
      have hxa : x ∈ Set.Icc a (a + 2 * Real.sqrt rho) := hE_a hxE
      have h_dist : dist x c ≤ Real.sqrt rho := by
        simp only [c, Real.dist_eq, abs_le]
        constructor <;> linarith [hxa.1, hxa.2]
      have h_dist2 : dist x c ≤ rho' := by linarith
      simpa [Metric.mem_closedBall] using h_dist2
    let center_set : Set ℝ := {c}
    have h_iscover : Metric.IsCover ε E_int center_set := by
      intro z hz
      have h_dist : dist z c ≤ rho' := hE_int_sub hz
      have h_edist : edist z c ≤ (ε : ENNReal) := by
        have h1 : edist z c = ENNReal.ofReal (dist z c) := edist_dist z c
        rw [h1]
        have h_coe1 : (ε : ENNReal) = ENNReal.ofReal (ε : ℝ) :=
          ENNReal.coe_nnreal_eq ε
        have h_coe2 : (ε : ℝ) = rho' := by
          have hε_def : ε = ⟨rho', hrho'_nonneg⟩ := by rfl
          rw [hε_def] <;> rfl
        rw [h_coe1, h_coe2]
        exact ENNReal.ofReal_le_ofReal h_dist
      exact ⟨c, by simp [center_set], h_edist⟩
    have h_le1 : Metric.externalCoveringNumber ε E_int ≤ center_set.encard :=
      h_iscover.externalCoveringNumber_le_encard
    have h_encard : center_set.encard = 1 := by
      simp [center_set, Set.encard_singleton]
    have h_le2 : Metric.externalCoveringNumber ε E_int ≤ (1 : ENat) := by
      rw [h_encard] at h_le1
      exact h_le1
    have h_le : (Metric.externalCoveringNumber ε E_int : ENNReal) ≤ 1 := by
      exact_mod_cast h_le2
    have h8 : 1 ≤ length / rho' := by
      rw [one_le_div hrho'_pos] <;> linarith
    have h9 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho') (1 - sigma) := by
      simp only [Kakeya.realRpowENN]
      have h10 : 1 ≤ Real.rpow (length / rho') (1 - sigma) := Real.one_le_rpow h8 (by linarith)
      exact ENNReal.one_le_ofReal.mpr h10
    have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN delta' (-outputLoss) * Kakeya.realRpowENN (length / rho') (1 - sigma) := by
      have h11 : (1 : ENNReal) ≤ Kakeya.realRpowENN delta' (-outputLoss) := hC_one
      have h12 : (1 : ENNReal) * (1 : ENNReal) ≤ Kakeya.realRpowENN delta' (-outputLoss) * Kakeya.realRpowENN (length / rho') (1 - sigma) := by gcongr
      simpa using h12
    exact h_le.trans h10
  · -- rho' ≤ √ρ
    have hrho'_le_sqrt : rho' ≤ Real.sqrt rho := by linarith
    have hrho'_le_one : rho' ≤ 1 := by linarith [hsqrt_le_one]
    by_cases h_short : length ≤ 2 * Real.sqrt rho
    · -- Short interval
      have hcov := hcover rho' hrho'_ge left length hlength
      have hcov' : (Metric.externalCoveringNumber ε E_int : ENNReal) ≤
          ENNReal.ofReal (C_count * length) * Kakeya.realRpowENN delta' (-2 - loss) := by
        simpa [hε_toNN] using hcov
      have h_pos1 : 0 ≤ C_count * length := by positivity
      have h1 : ENNReal.ofReal (C_count * length) * Kakeya.realRpowENN delta' (-2 - loss) ≤
          ENNReal.ofReal ((length / 2) * Real.rpow delta' (-outputLoss)) := by
        simp only [Kakeya.realRpowENN]
        have h_eq : ENNReal.ofReal (C_count * length) * ENNReal.ofReal (Real.rpow delta' (-2 - loss)) =
            ENNReal.ofReal (C_count * length * Real.rpow delta' (-2 - loss)) := by
          rw [← ENNReal.ofReal_mul h_pos1]
        rw [h_eq]
        exact ENNReal.ofReal_le_ofReal (h_mul_bound length hlength_pos)
      have h2 : (length / 2 : ℝ) ≤ (length / rho') ^ (1 - sigma) :=
        direct_counting_key_short hsigma_pos hsigma_lt_one hrho_pos hrho_le_one hrho'_pos hrho'_le_one hlength h_short
      have h3 : ENNReal.ofReal ((length / 2) * Real.rpow delta' (-outputLoss)) ≤
          Kakeya.realRpowENN delta' (-outputLoss) * Kakeya.realRpowENN (length / rho') (1 - sigma) := by
        have h_ineq : (length / 2) * Real.rpow delta' (-outputLoss) ≤
            Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma) := by
          calc (length / 2) * Real.rpow delta' (-outputLoss)
            = Real.rpow delta' (-outputLoss) * (length / 2) := by ring
          _ ≤ Real.rpow delta' (-outputLoss) * ((length / rho') ^ (1 - sigma)) := by
            exact mul_le_mul_of_nonneg_left h2 h_rpow_nonneg
        have h_ofReal : ENNReal.ofReal ((length / 2) * Real.rpow delta' (-outputLoss)) ≤
            ENNReal.ofReal (Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma)) :=
          ENNReal.ofReal_le_ofReal h_ineq
        have h_eq : ENNReal.ofReal (Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma)) =
            ENNReal.ofReal (Real.rpow delta' (-outputLoss)) * ENNReal.ofReal ((length / rho') ^ (1 - sigma)) :=
          ENNReal.ofReal_mul h_rpow_nonneg
        have h_final : ENNReal.ofReal ((length / 2) * Real.rpow delta' (-outputLoss)) ≤
            ENNReal.ofReal (Real.rpow delta' (-outputLoss)) * ENNReal.ofReal ((length / rho') ^ (1 - sigma)) := by
          rw [h_eq] at h_ofReal
          exact h_ofReal
        simpa [Kakeya.realRpowENN] using h_final
      exact hcov'.trans (h1.trans h3)
    · -- Long interval: apply hcover to bounding interval
      have h_long : 2 * Real.sqrt rho < length := by linarith
      let E_bounded := E ∩ Set.Icc a (a + 2 * Real.sqrt rho)
      have h_sub : E_int ⊆ E_bounded := by
        intro x hx; exact ⟨hx.1, hE_a hx.1⟩
      have h_cov_mono : (Metric.externalCoveringNumber ε E_int : ENNReal) ≤
          (Metric.externalCoveringNumber ε E_bounded : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
      have h_rho'_le : rho' ≤ 2 * Real.sqrt rho := by
        linarith [Real.sqrt_nonneg rho]
      have hcov_raw := hcover rho' hrho'_ge a (2 * Real.sqrt rho) h_rho'_le
      have hcov : (Metric.externalCoveringNumber ε E_bounded : ENNReal) ≤
          ENNReal.ofReal (C_count * (2 * Real.sqrt rho)) * Kakeya.realRpowENN delta' (-2 - loss) := by
        simpa [hε_toNN] using hcov_raw
      have h_pos1 : 0 ≤ C_count * (2 * Real.sqrt rho) := by positivity
      have h1 : ENNReal.ofReal (C_count * (2 * Real.sqrt rho)) * Kakeya.realRpowENN delta' (-2 - loss) ≤
          ENNReal.ofReal (Real.sqrt rho * Real.rpow delta' (-outputLoss)) := by
        simp only [Kakeya.realRpowENN]
        have h_eq : ENNReal.ofReal (C_count * (2 * Real.sqrt rho)) * ENNReal.ofReal (Real.rpow delta' (-2 - loss)) =
            ENNReal.ofReal (C_count * (2 * Real.sqrt rho) * Real.rpow delta' (-2 - loss)) := by
          rw [← ENNReal.ofReal_mul h_pos1]
        rw [h_eq]
        have h2 := h_mul_bound (2 * Real.sqrt rho) (by positivity)
        have h3 : (2 * Real.sqrt rho / 2 : ℝ) = Real.sqrt rho := by ring
        rw [h3] at h2
        exact ENNReal.ofReal_le_ofReal h2
      have h2 : Real.sqrt rho ≤ (length / rho') ^ (1 - sigma) :=
        direct_counting_key_long hsigma_pos hsigma_lt_one hrho_pos hrho_le_one hrho'_pos hrho'_le_one h_long
      have h3 : ENNReal.ofReal (Real.sqrt rho * Real.rpow delta' (-outputLoss)) ≤
          Kakeya.realRpowENN delta' (-outputLoss) * Kakeya.realRpowENN (length / rho') (1 - sigma) := by
        have h_ineq : Real.sqrt rho * Real.rpow delta' (-outputLoss) ≤
            Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma) := by
          calc Real.sqrt rho * Real.rpow delta' (-outputLoss)
            = Real.rpow delta' (-outputLoss) * Real.sqrt rho := by ring
          _ ≤ Real.rpow delta' (-outputLoss) * ((length / rho') ^ (1 - sigma)) := by
            exact mul_le_mul_of_nonneg_left h2 h_rpow_nonneg
        have h_ofReal : ENNReal.ofReal (Real.sqrt rho * Real.rpow delta' (-outputLoss)) ≤
            ENNReal.ofReal (Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma)) :=
          ENNReal.ofReal_le_ofReal h_ineq
        have h_eq : ENNReal.ofReal (Real.rpow delta' (-outputLoss) * (length / rho') ^ (1 - sigma)) =
            ENNReal.ofReal (Real.rpow delta' (-outputLoss)) * ENNReal.ofReal ((length / rho') ^ (1 - sigma)) :=
          ENNReal.ofReal_mul h_rpow_nonneg
        have h_final : ENNReal.ofReal (Real.sqrt rho * Real.rpow delta' (-outputLoss)) ≤
            ENNReal.ofReal (Real.rpow delta' (-outputLoss)) * ENNReal.ofReal ((length / rho') ^ (1 - sigma)) := by
          rw [h_eq] at h_ofReal
          exact h_ofReal
        simpa [Kakeya.realRpowENN] using h_final
      exact h_cov_mono.trans (hcov.trans (h1.trans h3))

/--
Construct local AD bounds from the base configuration and plane map.

Uses the HIGH case only: sticky data provides high multiplicity, which yields
propertyP → Córdoba slab bounds → slab_to_ad → AD bound (1-σ).

The LOW case (trivial covering) was dropped as mathematically insufficient.
-/
theorem pure_wz2_grain_local_ad
    {sigma loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss_src family shading)
    (cwa : WZ2PaperConvexWolffBound family (Kakeya.realRpowENN delta' (-loss_src)))
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneMap_unit : ∀ p, ‖planeMap p‖ = 1)
    (hplaneMap_incidence :
      ∀ (index : Fin family.card) (point : Point3),
        ∀ (hpoint : point ∈ shading.carrier index),
          |inner ℝ (family.tube index).direction
              (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 6 * delta')
    (hloss_src : 0 < loss_src)
    (hdelta'_pos : 0 < delta')
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (h_high : ∀ (rho : ℝ) (hrho : delta' ≤ rho) (hrho_le_one : rho ≤ 1)
        (q : Point3) (hq : q ∈ shading.union),
        Nonempty (PureWZ2LocalADHighData planeMap
          (Kakeya.realRpowENN delta' (-loss_src)) rho q hq)) :
    ∀ rho : ℝ, delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src)) := by
  intro rho hrho hrho_le_one point
  let q : Point3 := point
  have hq : q ∈ shading.union := point.prop
  let C : ENNReal := Kakeya.realRpowENN delta' (-loss_src)
  have h_high_data : Nonempty (PureWZ2LocalADHighData planeMap C rho q hq) :=
    h_high rho hrho hrho_le_one q hq
  rcases h_high_data with ⟨high'⟩
  -- HIGH case: use packaged slab data → slab_to_ad → AD bound
  have hC_one : (1 : ENNReal) ≤ C := by
    simp only [C, Kakeya.realRpowENN]
    have hdelta'_le_one : delta' ≤ 1 := extremal.delta_le_one
    have h4 : 1 ≤ Real.rpow delta' (-loss_src) := by
      have h : Real.rpow delta' (0 : ℝ) ≤ Real.rpow delta' (-loss_src) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta'_pos hdelta'_le_one (by linarith)
      have h5 : Real.rpow delta' (0 : ℝ) = 1 := by simp
      rw [h5] at h
      exact h
    have h9 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h9]
    exact ENNReal.ofReal_le_ofReal h4
  have hC_top : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have hsigma_pos : 0 < sigma := hsigma_pos
  have hsigma_lt_one : sigma < 1 := hsigma_lt_one
  have hrho_pos : 0 < rho := by linarith
  have h_ad_S : PureWZ2PaperADSet1
      (scalarProjection high'.v high'.S) rho (1 - sigma) C :=
    slab_to_ad
      high'.hv_unit high'.hS_meas high'.W high'.V_min high'.V_total
      high'.hW_pos high'.hVmin_pos high'.hV_total_pos high'.hV_total
      high'.h_slab hrho_pos hsigma_pos hsigma_lt_one hC_one hC_top high'.h_arithmetic
  have h_dir : high'.v = planeMap ⟨q, hq⟩ := high'.h_dir
  have h_target_sub : (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ⊆ high'.S := high'.h_contain
  have h_proj_sub : scalarProjection (planeMap ⟨q, hq⟩)
      (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ⊆
      scalarProjection high'.v high'.S := by
    rw [← high'.h_dir]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, high'.h_contain hx, rfl⟩
  have h_ad_target : PureWZ2PaperADSet1
      (scalarProjection (planeMap ⟨q, hq⟩)
        (shading.union ∩ Metric.closedBall q (Real.sqrt rho)))
      rho (1 - sigma) C := by
    rcases h_ad_S with ⟨h1, h2, h3, h4, h5, h6⟩
    refine' ⟨h1, h2, h3, h4, h5, _⟩
    intro rho' hrho' hdelta left length hlen
    let E_small := scalarProjection (planeMap ⟨q, hq⟩)
        (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ∩ Set.Icc left (left + length)
    let E_large := scalarProjection high'.v high'.S ∩ Set.Icc left (left + length)
    have h7 : E_small ⊆ E_large := by
      intro x hx
      exact ⟨h_proj_sub hx.1, hx.2⟩
    have h8 : (Metric.externalCoveringNumber ⟨rho', hrho'⟩ E_small) ≤
              Metric.externalCoveringNumber ⟨rho', hrho'⟩ E_large :=
      Metric.externalCoveringNumber_mono_set h7
    have h9 : (↑(Metric.externalCoveringNumber ⟨rho', hrho'⟩ E_large) : ENNReal) ≤
               C * Kakeya.realRpowENN (length / rho') (1 - sigma) :=
      h6 rho' hrho' hdelta left length hlen
    have h10 : (↑(Metric.externalCoveringNumber ⟨rho', hrho'⟩ E_small) : ENNReal) ≤
               (↑(Metric.externalCoveringNumber ⟨rho', hrho'⟩ E_large) : ENNReal) := by
      exact_mod_cast h8
    exact h10.trans h9
  exact h_ad_target

/-!
## Dichotomy construction

Wires sticky data → propertyP → Córdoba → HighData for the HIGH case,
and trivial volume bounds for the LOW case.

### Open sub-goals

1. **Constant planeMap incidence**: For `v = planeMap ⟨q, hq⟩`, show
   `|inner(coarse.tube i).direction v| ≤ 6L` for all coarse tubes in
   propertyOne. Uses Lipschitz property of planeMap, direction closeness
   between fine and coarse tubes, and the original incidence bound.

2. **Parameter arithmetic**: Choose `L`, `tau`, `epsilon₁`, `epsilon₃`
   such that `(V_total/V_min) * (2W/rho + 2) ≤ C`.

3. **Containment**: Show `shading.union ∩ ball(q, sqrt(rho)) ⊆ S`
   where `S` is the Córdoba slab domain.

4. **Sticky data at arbitrary scale**: Derive sticky-like conditions
   (balanced cover, high multiplicity) from the extremal configuration
   at any requested coarse scale `L`.
-/

/--
Construct the local AD dichotomy from a cropped extremal configuration
and plane map.

For coarse scales (`rho ≥ delta'^(sigma/(1-sigma))`), the trivial volume
upper bound suffices (LOW case). For finer scales, the caller supplies
HIGH case data (typically constructed from sticky data → PropertyP →
Córdoba slab bounds).

The `h_high_case` hypothesis packages the HIGH case construction so this
lemma can focus on the case split. See `HardRegimeHighCaseAD` and
`HighCaseToHighData` for how to construct it from sticky data.
-/
theorem pure_wz2_grain_local_dichotomy
    {sigma loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss_src family shading)
    (cwa : WZ2PaperConvexWolffBound family (Kakeya.realRpowENN delta' (-loss_src)))
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneMap_unit : ∀ p, ‖planeMap p‖ = 1)
    (hplaneMap_lip : LipschitzWith 6 planeMap)
    (hplaneMap_incidence :
      ∀ (index : Fin family.card) (point : Point3),
        ∀ (hpoint : point ∈ shading.carrier index),
          |inner ℝ (family.tube index).direction
              (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 6 * delta')
    (hloss_src : 0 < loss_src)
    (hdelta'_pos : 0 < delta')
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (h_high_case : ∀ (rho : ℝ) (hrho : delta' ≤ rho) (q : Point3)
        (hq : q ∈ shading.union),
        ¬(delta' ^ sigma ≤ rho ^ (1 - sigma)) →
        Nonempty (PureWZ2LocalADHighData planeMap
          (Kakeya.realRpowENN delta' (-loss_src)) rho q hq)) :
    PureWZ2LocalADDichotomy
      (sigma := sigma) (loss_src := loss_src)
      (family := family) (shading := shading)
      planeMap (Kakeya.realRpowENN delta' (-loss_src)) := by
  let C : ENNReal := Kakeya.realRpowENN delta' (-loss_src)
  refine' ⟨_⟩
  intro rho hrho q hq
  -- Case split on whether rho is large enough for trivial bound
  by_cases h_trivial : delta' ^ sigma ≤ rho ^ (1 - sigma)
  · -- LOW case: trivial volume bound from extremal volume upper
    have h1 : volume (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ≤
          volume shading.union := by
      have hsub : (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ⊆ shading.union := by
        intro x hx
        exact hx.1
      exact measure_mono hsub
    have h2 : volume shading.union ≤
          Kakeya.realRpowENN delta' (sigma - loss_src) :=
      extremal.volume_upper
    have h3 : Kakeya.realRpowENN delta' (sigma - loss_src) =
          Kakeya.realRpowENN delta' sigma * Kakeya.realRpowENN delta' (-loss_src) := by
      simp only [Kakeya.realRpowENN]
      have h41 : sigma - loss_src = sigma + (-loss_src) := by ring
      rw [h41]
      have h4 : Real.rpow delta' (sigma + (-loss_src)) =
            Real.rpow delta' sigma * Real.rpow delta' (-loss_src) :=
        Real.rpow_add hdelta'_pos sigma (-loss_src)
      rw [h4]
      have h5 : 0 ≤ Real.rpow delta' sigma := Real.rpow_nonneg hdelta'_pos.le _
      rw [ENNReal.ofReal_mul h5]
    have h6 : Kakeya.realRpowENN delta' sigma ≤
          Kakeya.realRpowENN rho (1 - sigma) := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_le_ofReal h_trivial
    have h7 : volume (shading.union ∩ Metric.closedBall q (Real.sqrt rho)) ≤
          Kakeya.realRpowENN delta' (-loss_src) * Kakeya.realRpowENN rho (1 - sigma) := by
      calc
        volume (shading.union ∩ Metric.closedBall q (Real.sqrt rho))
          ≤ volume shading.union := h1
        _ ≤ Kakeya.realRpowENN delta' (sigma - loss_src) := h2
        _ = Kakeya.realRpowENN delta' sigma * Kakeya.realRpowENN delta' (-loss_src) := h3
        _ ≤ Kakeya.realRpowENN rho (1 - sigma) * Kakeya.realRpowENN delta' (-loss_src) := by
          gcongr
        _ = Kakeya.realRpowENN delta' (-loss_src) * Kakeya.realRpowENN rho (1 - sigma) := by
          rw [mul_comm]
    exact Or.inr h7
  · -- HIGH case: use caller-supplied HighData (from sticky data + PropertyP + Córdoba)
    have h_high : Nonempty (PureWZ2LocalADHighData planeMap C rho q hq) :=
      h_high_case rho hrho q hq h_trivial
    exact Or.inl h_high

end Kakeya.Assouad

end
