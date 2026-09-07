import MyLeanRepo.Kakeya.Assouad.CoveringInfrastructure
import MyLeanRepo.Kakeya.Assouad.RefinementInfrastructure

/-!
# Measurable point-multiplicity band refinements

This is the canonical shading refinement used in WZ2 Section 6: outside the
chosen slab the shading is unchanged, while inside the slab only points whose
old point multiplicity lies in the selected band are retained.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Point multiplicity is a measurable finite sum of measurable indicators. -/
lemma measurable_pointMultiplicity
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) :
    Measurable Y.pointMultiplicity := by
  classical
  have hpoint :
      Y.pointMultiplicity =
        fun p =>
          ∑ i ∈ (Finset.univ : Finset (Fin F.card)),
            if p ∈ Y.carrier i then 1 else 0 := by
    funext p
    rw [Kakeya.Streamlined.Shading.pointMultiplicity,
      Finset.card_filter]
  rw [hpoint]
  exact Finset.measurable_sum Finset.univ (by
    intro i _
    exact Measurable.ite (Y.measurable_carrier i)
      measurable_const measurable_const)

/-- Point multiplicity is the finite sum of the carrier indicators. -/
lemma coe_pointMultiplicity_eq_sum_indicator
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (p : Point3) :
    (Y.pointMultiplicity p : ENNReal) =
      ∑ i : Fin F.card,
        (Y.carrier i).indicator (fun _ => (1 : ENNReal)) p := by
  classical
  rw [Kakeya.Streamlined.Shading.pointMultiplicity,
    Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p ∈ Y.carrier i
  · simp [hp]
  · simp [hp]

/-- Finite Fubini: the integral of point multiplicity is total shaded mass. -/
lemma lintegral_pointMultiplicity
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) :
    (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) = Y.mass := by
  calc
    (∫⁻ p, (Y.pointMultiplicity p : ENNReal))
        = ∫⁻ p, ∑ i : Fin F.card,
            (Y.carrier i).indicator (fun _ => (1 : ENNReal)) p := by
          apply MeasureTheory.lintegral_congr
          exact coe_pointMultiplicity_eq_sum_indicator Y
    _ = ∑ i : Fin F.card,
          ∫⁻ p, (Y.carrier i).indicator
            (fun _ => (1 : ENNReal)) p := by
          rw [MeasureTheory.lintegral_finset_sum]
          intro i _
          exact measurable_const.indicator (Y.measurable_carrier i)
    _ = ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact MeasureTheory.lintegral_indicator_one
            (Y.measurable_carrier i)
    _ = Y.mass := rfl

/--
Finite Fubini on an arbitrary measurable set: the shaded mass restricted to
`S` is the point-multiplicity integral over `S`.
-/
lemma sum_volume_inter_eq_setLIntegral_pointMultiplicity
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    {S : Set Point3} (hS : MeasurableSet S) :
    ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i ∩ S) =
      ∫⁻ p in S, (Y.pointMultiplicity p : ENNReal) := by
  symm
  calc
    (∫⁻ p in S, (Y.pointMultiplicity p : ENNReal))
        = ∫⁻ p in S, ∑ i : Fin F.card,
            (Y.carrier i).indicator (fun _ => (1 : ENNReal)) p := by
          apply MeasureTheory.lintegral_congr
          exact coe_pointMultiplicity_eq_sum_indicator Y
    _ = ∑ i : Fin F.card,
          ∫⁻ p in S, (Y.carrier i).indicator
            (fun _ => (1 : ENNReal)) p := by
          rw [MeasureTheory.lintegral_finset_sum]
          intro i _
          exact measurable_const.indicator (Y.measurable_carrier i)
    _ = ∑ i : Fin F.card,
          MeasureTheory.volume (Y.carrier i ∩ S) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [MeasureTheory.setLIntegral_indicator
            (Y.measurable_carrier i)]
          rw [MeasureTheory.setLIntegral_one]

/-- The measurable set where the old point multiplicity lies in an ENNReal band. -/
def multiplicityBand
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (lower upper : ENNReal) : Set Point3 :=
  {p |
    lower ≤ (Y.pointMultiplicity p : ENNReal) ∧
      (Y.pointMultiplicity p : ENNReal) ≤ upper}

lemma measurableSet_multiplicityBand
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (lower upper : ENNReal) :
    MeasurableSet (multiplicityBand Y lower upper) := by
  let allowed : Set ℕ :=
    {n |
      lower ≤ (n : ENNReal) ∧
        (n : ENNReal) ≤ upper}
  change MeasurableSet (Y.pointMultiplicity ⁻¹' allowed)
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_pointMultiplicity Y)

/-- A horizontal slab is measurable. -/
lemma measurableSet_horizontalSlab (a b : ℝ) :
    MeasurableSet (horizontalSlab a b) := by
  have hcoord : Continuous (fun p : Point3 => p (2 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  change MeasurableSet ((fun p : Point3 => p (2 : Fin 3)) ⁻¹' Set.Icc a b)
  exact measurableSet_Icc.preimage hcoord.measurable

/-- A finite shaded union is measurable. -/
lemma measurableSet_shading_union
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) :
    MeasurableSet Y.union := by
  have hunion :
      Y.union = ⋃ i : Fin F.card, Y.carrier i := by
    ext p
    simp [Kakeya.Streamlined.Shading.union]
  rw [hunion]
  exact MeasurableSet.iUnion fun i => Y.measurable_carrier i

/-- Restrict every shaded carrier to a horizontal slab. -/
def slabRestriction
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (a b : ℝ) :
    Kakeya.Streamlined.Shading F where
  carrier i := Y.carrier i ∩ horizontalSlab a b
  measurable_carrier i :=
    (Y.measurable_carrier i).inter (measurableSet_horizontalSlab a b)
  subset_body i := (Y.carrier i).inter_subset_left.trans (Y.subset_body i)

@[simp]
lemma slabRestriction_mass
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (a b : ℝ) :
    (slabRestriction Y a b).mass = shadedMassInSlab Y a b := rfl

lemma pointMultiplicity_slabRestriction
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (a b : ℝ)
    {p : Point3} (hp : p ∈ horizontalSlab a b) :
    (slabRestriction Y a b).pointMultiplicity p =
      Y.pointMultiplicity p := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [slabRestriction, hp]

/-- Slab Fubini identity in the form used by the multiplicity refinement. -/
lemma lintegral_slab_pointMultiplicity
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (a b : ℝ) :
    (∫⁻ p, ((slabRestriction Y a b).pointMultiplicity p : ENNReal)) =
      shadedMassInSlab Y a b := by
  rw [lintegral_pointMultiplicity, slabRestriction_mass]

/--
Keep the old shading outside `[a,b]`; inside the slab, retain exactly the old
points whose old multiplicity lies in `[lower,upper]`.
-/
def multiplicityBandSubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal) :
    Kakeya.Streamlined.Shading F where
  carrier i :=
    (Y.carrier i \ horizontalSlab a b) ∪
      (Y.carrier i ∩ horizontalSlab a b ∩
        multiplicityBand Y lower upper)
  measurable_carrier i :=
    ((Y.measurable_carrier i).diff (measurableSet_horizontalSlab a b)).union
      (((Y.measurable_carrier i).inter (measurableSet_horizontalSlab a b)).inter
        (measurableSet_multiplicityBand Y lower upper))
  subset_body i := by
    intro p hp
    rcases hp with hp | hp
    · exact Y.subset_body i hp.1
    · exact Y.subset_body i hp.1.1

lemma multiplicityBandSubshading_isSubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal) :
    IsSubshading (multiplicityBandSubshading Y a b lower upper) Y := by
  intro i p hp
  rcases hp with hp | hp
  · exact hp.1
  · exact hp.1.1

/-- Inside the selected slab, each refined carrier is exactly the old band part. -/
lemma multiplicityBandSubshading_carrier_inter_slab
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal)
    (i : Fin F.card) :
    (multiplicityBandSubshading Y a b lower upper).carrier i ∩
        horizontalSlab a b =
      Y.carrier i ∩ horizontalSlab a b ∩
        multiplicityBand Y lower upper := by
  ext p
  simp only [multiplicityBandSubshading, Set.mem_inter_iff,
    Set.mem_union, Set.mem_diff]
  aesop

/-- The refined shaded union inside the slab is exactly the old union's band part. -/
lemma multiplicityBandSubshading_union_inter_slab
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal) :
    (multiplicityBandSubshading Y a b lower upper).union ∩
        horizontalSlab a b =
      Y.union ∩ horizontalSlab a b ∩
        multiplicityBand Y lower upper := by
  ext p
  constructor
  · rintro ⟨⟨i, hp⟩, hp_slab⟩
    have hp' :
        p ∈ Y.carrier i ∩ horizontalSlab a b ∩
          multiplicityBand Y lower upper := by
      rw [← multiplicityBandSubshading_carrier_inter_slab
        Y a b lower upper i]
      exact ⟨hp, hp_slab⟩
    exact ⟨⟨⟨i, hp'.1.1⟩, hp'.1.2⟩, hp'.2⟩
  · rintro ⟨⟨⟨i, hp⟩, hp_slab⟩, hp_band⟩
    refine ⟨⟨i, ?_⟩, hp_slab⟩
    exact Or.inr ⟨⟨hp, hp_slab⟩, hp_band⟩

/-- The refined slab mass is the old shaded mass restricted to the band. -/
lemma shadedMassInSlab_multiplicityBandSubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal) :
    shadedMassInSlab
        (multiplicityBandSubshading Y a b lower upper) a b =
      ∑ i : Fin F.card,
        MeasureTheory.volume
          (Y.carrier i ∩ horizontalSlab a b ∩
            multiplicityBand Y lower upper) := by
  simp only [shadedMassInSlab]
  apply Finset.sum_congr rfl
  intro i _
  rw [multiplicityBandSubshading_carrier_inter_slab
    Y a b lower upper i]

/-- The set of slab points below a prescribed old-multiplicity threshold. -/
def lowMultiplicitySet
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) : Set Point3 :=
  Y.union ∩ horizontalSlab a b ∩
    {p | (Y.pointMultiplicity p : ENNReal) < threshold}

lemma measurableSet_lowMultiplicitySet
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    MeasurableSet (lowMultiplicitySet Y a b threshold) := by
  apply ((measurableSet_shading_union Y).inter
    (measurableSet_horizontalSlab a b)).inter
  let allowed : Set ℕ :=
    {n | (n : ENNReal) < threshold}
  change MeasurableSet (Y.pointMultiplicity ⁻¹' allowed)
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_pointMultiplicity Y)

/-- Total old shaded mass carried by slab points below `threshold`. -/
def lowMultiplicityMass
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) : ENNReal :=
  ∑ i : Fin F.card,
    MeasureTheory.volume
      (Y.carrier i ∩ lowMultiplicitySet Y a b threshold)

/--
The low-multiplicity tail is bounded by `threshold` times the volume of the
whole shaded slab.
-/
lemma lowMultiplicityMass_le
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    lowMultiplicityMass Y a b threshold ≤
      threshold *
        MeasureTheory.volume (Y.union ∩ horizontalSlab a b) := by
  change
    (∑ i : Fin F.card,
      MeasureTheory.volume
        (Y.carrier i ∩ lowMultiplicitySet Y a b threshold)) ≤ _
  rw [sum_volume_inter_eq_setLIntegral_pointMultiplicity Y
    (measurableSet_lowMultiplicitySet Y a b threshold)]
  calc
    (∫⁻ p in lowMultiplicitySet Y a b threshold,
        (Y.pointMultiplicity p : ENNReal))
        ≤ ∫⁻ _p in lowMultiplicitySet Y a b threshold,
            threshold := by
          apply MeasureTheory.setLIntegral_mono'
            (measurableSet_lowMultiplicitySet Y a b threshold)
          intro p hp
          exact hp.2.le
    _ = threshold *
        MeasureTheory.volume (lowMultiplicitySet Y a b threshold) := by
          rw [MeasureTheory.setLIntegral_const]
    _ ≤ threshold *
        MeasureTheory.volume (Y.union ∩ horizontalSlab a b) := by
          gcongr
          intro p hp
          exact hp.1

/--
Combining the low-tail estimate with a finite ball cover gives the explicit
bound used by the large-slope refinement.
-/
lemma lowMultiplicityMass_le_of_cover
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    {a b : ℝ} (hab : a ≤ b)
    {threshold N : ENNReal}
    (hcover :
      CanCoverByBalls (Y.union ∩ horizontalSlab a b) (b - a) N) :
    lowMultiplicityMass Y a b threshold ≤
      threshold * (N * ENNReal.ofReal (8 * (b - a) ^ 3)) := by
  exact (lowMultiplicityMass_le Y a b threshold).trans
    (mul_le_mul_left' (hcover.volume_le (sub_nonneg.mpr hab)) threshold)

/-- Shaded slab points strictly above a prescribed old-multiplicity threshold. -/
def highMultiplicitySet
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) : Set Point3 :=
  Y.union ∩ horizontalSlab a b ∩
    {p | threshold < (Y.pointMultiplicity p : ENNReal)}

lemma measurableSet_highMultiplicitySet
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    MeasurableSet (highMultiplicitySet Y a b threshold) := by
  apply ((measurableSet_shading_union Y).inter
    (measurableSet_horizontalSlab a b)).inter
  let allowed : Set ℕ :=
    {n | threshold < (n : ENNReal)}
  change MeasurableSet (Y.pointMultiplicity ⁻¹' allowed)
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_pointMultiplicity Y)

/-- The old shading restricted to its high-multiplicity slab points. -/
def highMultiplicitySubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    Kakeya.Streamlined.Shading F where
  carrier i := Y.carrier i ∩ highMultiplicitySet Y a b threshold
  measurable_carrier i :=
    (Y.measurable_carrier i).inter
      (measurableSet_highMultiplicitySet Y a b threshold)
  subset_body i := (Y.carrier i).inter_subset_left.trans (Y.subset_body i)

lemma highMultiplicitySubshading_isSubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    IsSubshading (highMultiplicitySubshading Y a b threshold) Y := by
  intro i
  exact Set.inter_subset_left

lemma highMultiplicitySubshading_union
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    (highMultiplicitySubshading Y a b threshold).union =
      highMultiplicitySet Y a b threshold := by
  ext p
  constructor
  · rintro ⟨i, hp⟩
    exact hp.2
  · intro hp
    rcases hp.1.1 with ⟨i, hp_i⟩
    exact ⟨i, hp_i, hp⟩

lemma highMultiplicitySubshading_pointMultiplicity
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal)
    {p : Point3} (hp : p ∈ highMultiplicitySet Y a b threshold) :
    (highMultiplicitySubshading Y a b threshold).pointMultiplicity p =
      Y.pointMultiplicity p := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [highMultiplicitySubshading, hp]

/-- Total shaded mass in the high-multiplicity part of the slab. -/
def highMultiplicityMass
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) : ENNReal :=
  (highMultiplicitySubshading Y a b threshold).mass

/-- High multiplicity forces `threshold * union volume` below high shaded mass. -/
lemma threshold_mul_volume_highMultiplicitySet_le
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (threshold : ENNReal) :
    threshold *
        MeasureTheory.volume (highMultiplicitySet Y a b threshold) ≤
      highMultiplicityMass Y a b threshold := by
  rw [highMultiplicityMass, ← lintegral_pointMultiplicity]
  calc
    threshold *
        MeasureTheory.volume (highMultiplicitySet Y a b threshold)
        = ∫⁻ _p in highMultiplicitySet Y a b threshold, threshold := by
            rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ p in highMultiplicitySet Y a b threshold,
          ((highMultiplicitySubshading Y a b threshold).pointMultiplicity p :
            ENNReal) := by
          apply MeasureTheory.setLIntegral_mono'
            (measurableSet_highMultiplicitySet Y a b threshold)
          intro p hp
          rw [highMultiplicitySubshading_pointMultiplicity
            Y a b threshold hp]
          exact hp.2.le
    _ ≤ ∫⁻ p,
          ((highMultiplicitySubshading Y a b threshold).pointMultiplicity p :
            ENNReal) := by
          exact MeasureTheory.setLIntegral_le_lintegral
            (μ := MeasureTheory.volume)
            (highMultiplicitySet Y a b threshold)
            (fun p : Point3 =>
              ((highMultiplicitySubshading Y a b threshold).pointMultiplicity p :
                ENNReal))

lemma pointMultiplicity_multiplicityBandSubshading
    {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F)
    (a b : ℝ) (lower upper : ENNReal)
    {p : Point3} (hp_slab : p ∈ horizontalSlab a b)
    (hp_band : p ∈ multiplicityBand Y lower upper) :
    (multiplicityBandSubshading Y a b lower upper).pointMultiplicity p =
      Y.pointMultiplicity p := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hp
    rcases hp with hp | hp
    · exact hp.1
    · exact hp.1.1
  · intro hp
    exact Or.inr ⟨⟨hp, hp_slab⟩, hp_band⟩

/-- The band refinement has exactly the requested pointwise bounds in the slab. -/
lemma multiplicityBandSubshading_hasRefinedPointMultiplicityInSlab
    {delta sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (a b : ℝ) :
    HasRefinedPointMultiplicityInSlab
      (multiplicityBandSubshading Y a b
        (Kakeya.realRpowENN delta (2 - sigma + 2 * eta) * F.enncard)
        (Kakeya.realRpowENN delta (2 - sigma - 2 * eta) * F.enncard))
      sigma eta a b := by
  intro p hp
  let lower :=
    Kakeya.realRpowENN delta (2 - sigma + 2 * eta) * F.enncard
  let upper :=
    Kakeya.realRpowENN delta (2 - sigma - 2 * eta) * F.enncard
  have hp_slab : p ∈ horizontalSlab a b := hp.2
  rcases hp.1 with ⟨i, hp_i⟩
  have hp_band : p ∈ multiplicityBand Y lower upper := by
    rcases hp_i with hp_outside | hp_inside
    · exact (hp_outside.2 hp_slab).elim
    · exact hp_inside.2
  have hmult :=
    pointMultiplicity_multiplicityBandSubshading
      Y a b lower upper hp_slab hp_band
  change lower ≤ (Y.pointMultiplicity p : ENNReal) ∧
    (Y.pointMultiplicity p : ENNReal) ≤ upper at hp_band
  change lower ≤
      ((multiplicityBandSubshading Y a b lower upper).pointMultiplicity p :
        ENNReal) ∧
    ((multiplicityBandSubshading Y a b lower upper).pointMultiplicity p :
        ENNReal) ≤ upper
  rw [hmult]
  exact hp_band

end Kakeya.Assouad
