import Kakeya.Sticky.Definitions
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConcreteABI

/-!
# Exact geometric bridge to the competitor tube model

The two developments use the same closed neighbourhood of a unit segment,
but package the segment differently.  This file records the lossless
conversion in both directions.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Integration

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- The endpoint presentation used by the competitor, viewed as our
base-and-direction `DeltaTube`. -/
def competitorTubeToDeltaTube {δ : NNReal} (T : Tube δ Space3) :
    Kakeya.DeltaTube (δ : ℝ) where
  base := T.x
  direction := T.y - T.x
  direction_unit := T.norm_direction

lemma competitorTube_unitSegment_eq {δ : NNReal} (T : Tube δ Space3) :
    Kakeya.unitSegment T.x (T.y - T.x) = segment ℝ T.x T.y := by
  rw [segment_eq_image']
  rfl

@[simp] theorem competitorTubeToDeltaTube_base {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).base = T.x := rfl

@[simp] theorem competitorTubeToDeltaTube_direction {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).direction = T.direction := rfl

@[simp] theorem competitorTubeToDeltaTube_endpoint {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).base +
        (competitorTubeToDeltaTube T).direction = T.y := by
  simp [competitorTubeToDeltaTube]

theorem competitorTubeToDeltaTube_midpoint {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).base +
        (1 / 2 : ℝ) • (competitorTubeToDeltaTube T).direction = T.center := by
  simp only [competitorTubeToDeltaTube, Tube.center]
  rw [midpoint_eq_smul_add, invOf_eq_inv]
  module

@[simp] theorem competitorTubeToDeltaTube_carrier {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).carrier = T.carrier := by
  change Metric.cthickening (δ : ℝ)
      (Kakeya.unitSegment T.x (T.y - T.x)) = T.carrier
  rw [competitorTube_unitSegment_eq,
    T.carrier_eq, ← isClosed_segment.cthickening_eq_biUnion_closedBall δ.coe_nonneg]

@[simp] theorem competitorTubeToDeltaTube_volume {δ : NNReal}
    (T : Tube δ Space3) :
    (competitorTubeToDeltaTube T).volume = volume T.carrier := by
  rw [Kakeya.DeltaTube.volume, competitorTubeToDeltaTube_carrier]

/-- Our base-and-direction presentation, viewed as a competitor tube with
endpoints `base` and `base + direction`. -/
def deltaTubeToCompetitorTube {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) : Tube δ Space3 :=
  Tube.mk' δ (x := T.base) (y := T.base + T.direction) (by
    simpa [dist_eq_norm] using T.direction_unit)

@[simp] theorem deltaTubeToCompetitorTube_x {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    (deltaTubeToCompetitorTube T).x = T.base := rfl

@[simp] theorem deltaTubeToCompetitorTube_direction {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    (deltaTubeToCompetitorTube T).direction = T.direction := by
  simp [deltaTubeToCompetitorTube, Tube.direction]

@[simp] theorem deltaTubeToCompetitorTube_y {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    (deltaTubeToCompetitorTube T).y = T.base + T.direction := rfl

theorem deltaTubeToCompetitorTube_midpoint {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    (deltaTubeToCompetitorTube T).center =
        T.base + (1 / 2 : ℝ) • T.direction := by
  change midpoint ℝ T.base (T.base + T.direction) =
    T.base + (1 / 2 : ℝ) • T.direction
  have h := midpoint_sub_left (R := ℝ) T.base (T.base + T.direction)
  rw [invOf_eq_inv] at h
  apply sub_eq_zero.mp
  calc
    midpoint ℝ T.base (T.base + T.direction) -
          (T.base + (1 / 2 : ℝ) • T.direction) =
        (midpoint ℝ T.base (T.base + T.direction) - T.base) -
          (1 / 2 : ℝ) • T.direction := by abel
    _ = 0 := by rw [h]; module

@[simp] theorem deltaTubeToCompetitorTube_carrier {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    (deltaTubeToCompetitorTube T).carrier = T.carrier := by
  rw [Tube.carrier_eq_cthickening, Kakeya.DeltaTube.carrier]
  congr 1
  rw [segment_eq_image']
  simp [deltaTubeToCompetitorTube, Kakeya.unitSegment]

@[simp] theorem deltaTubeToCompetitorTube_volume {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    volume (deltaTubeToCompetitorTube T).carrier = T.volume := by
  rw [deltaTubeToCompetitorTube_carrier]
  rfl

@[simp] theorem competitorTube_roundtrip {δ : NNReal}
    (T : Tube δ Space3) :
    deltaTubeToCompetitorTube (competitorTubeToDeltaTube T) = T := by
  apply Tube.ext
  · rw [deltaTubeToCompetitorTube_carrier, competitorTubeToDeltaTube_carrier]
  · rfl
  · simp [deltaTubeToCompetitorTube, competitorTubeToDeltaTube]

@[simp] theorem deltaTube_roundtrip {δ : NNReal}
    (T : Kakeya.DeltaTube (δ : ℝ)) :
    competitorTubeToDeltaTube (deltaTubeToCompetitorTube T) = T := by
  cases T
  simp [competitorTubeToDeltaTube, deltaTubeToCompetitorTube]

/-- The competitor overlap notion of essential distinctness is exactly the
WZ2 `DeltaTube` notion after converting the two tubes. -/
theorem competitorTube_essentiallyDistinct_iff {δ : NNReal}
    (T U : Tube δ Space3) :
    (competitorTubeToDeltaTube T).EssentiallyDistinct
        (competitorTubeToDeltaTube U) ↔
      _root_.IsEssentiallyDistinct T.carrier U.carrier := by
  simp only [Kakeya.DeltaTube.EssentiallyDistinct, _root_.IsEssentiallyDistinct,
    competitorTubeToDeltaTube_carrier, Kakeya.DeltaTube.volume]
  rw [one_div]

section FiniteFamily

variable {ι : Type*}

/-- The explicit equivalence between the WZ2 finite index type and the
competitor finset subtype. -/
def competitorIndexEquiv (s : Finset ι) : Fin s.card ≃ s :=
  s.equivFin.symm

/-- The canonical enumeration of a competitor finset. -/
def competitorIndex (s : Finset ι) (i : Fin s.card) : ι :=
  (competitorIndexEquiv s i).1

@[simp] theorem competitorIndex_mem (s : Finset ι) (i : Fin s.card) :
    competitorIndex s i ∈ s :=
  (competitorIndexEquiv s i).2

/-- A finite competitor tube family, without shadings, in the indexed WZ2
representation.  This is also used for node families of a competitor uniform
hierarchy. -/
def competitorPlainTubeFamily {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ Space3) :
    Kakeya.Streamlined.TubeFamily (δ : ℝ) where
  card := s.card
  tube i := competitorTubeToDeltaTube (T (competitorIndex s i))

@[simp] theorem competitorPlainTubeFamily_card {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ Space3) :
    (competitorPlainTubeFamily s T).card = s.card := rfl

@[simp] theorem competitorPlainTubeFamily_tube {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ Space3) (i : Fin s.card) :
    (competitorPlainTubeFamily s T).tube i =
      competitorTubeToDeltaTube (T (competitorIndex s i)) := rfl

@[simp] theorem competitorPlainTubeFamily_carrier {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ Space3) (i : Fin s.card) :
    ((competitorPlainTubeFamily s T).tube i).carrier =
      (T (competitorIndex s i)).carrier := by
  rw [competitorPlainTubeFamily_tube, competitorTubeToDeltaTube_carrier]

/-- A competitor finite tube family in the indexed WZ2 representation. -/
def competitorTubeFamily {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    Kakeya.Streamlined.TubeFamily (δ : ℝ) where
  card := s.card
  tube i := competitorTubeToDeltaTube (V (competitorIndex s i)).toTube

@[simp] theorem competitorTubeFamily_card {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    (competitorTubeFamily s V).card = s.card := rfl

@[simp] theorem competitorTubeFamily_tube {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) (i : Fin s.card) :
    (competitorTubeFamily s V).tube i =
      competitorTubeToDeltaTube (V (competitorIndex s i)).toTube := rfl

@[simp] theorem competitorTubeFamily_carrier {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) (i : Fin s.card) :
    ((competitorTubeFamily s V).tube i).carrier =
      (V (competitorIndex s i)).carrier := by
  rw [competitorTubeFamily_tube, competitorTubeToDeltaTube_carrier]

/-- Pairwise overlap essential distinctness is preserved and reflected by the
canonical enumeration of a competitor family.  In particular this converts
the exact output of the competitor's essential-distinctness cleanup into the
source-family premise required by the WZ2 reanchored bridge. -/
theorem competitorTubeFamily_isEssentiallyDistinct_iff {δ : NNReal}
    (s : Finset ι) (V : ι → ShadedTube δ Space3) :
    (competitorTubeFamily s V).IsEssentiallyDistinct ↔
      (s : Set ι).Pairwise (fun i j =>
        _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) := by
  constructor
  · intro h i hi j hj hij
    let ii : Fin s.card := s.equivFin ⟨i, hi⟩
    let jj : Fin s.card := s.equivFin ⟨j, hj⟩
    have hii : competitorIndex s ii = i := by
      simp [ii, competitorIndex, competitorIndexEquiv]
    have hjj : competitorIndex s jj = j := by
      simp [jj, competitorIndex, competitorIndexEquiv]
    have hij' : ii ≠ jj := by
      intro heq
      apply hij
      rw [← hii, ← hjj, heq]
    have hconverted := h ii jj hij'
    rw [competitorTubeFamily_tube, competitorTubeFamily_tube,
      competitorTube_essentiallyDistinct_iff, hii, hjj] at hconverted
    exact hconverted
  · intro h i j hij
    have hsource_ne : competitorIndex s i ≠ competitorIndex s j := by
      intro heq
      apply hij
      apply (competitorIndexEquiv s).injective
      exact Subtype.ext heq
    rw [competitorTubeFamily_tube, competitorTubeFamily_tube,
      competitorTube_essentiallyDistinct_iff]
    exact h (competitorIndex_mem s i)
      (competitorIndex_mem s j) hsource_ne

/-- The corresponding equivalence for an unshaded competitor tube family. -/
theorem competitorPlainTubeFamily_isEssentiallyDistinct_iff {δ : NNReal}
    (s : Finset ι) (T : ι → Tube δ Space3) :
    (competitorPlainTubeFamily s T).IsEssentiallyDistinct ↔
      (s : Set ι).Pairwise (fun i j =>
        _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
  constructor
  · intro h i hi j hj hij
    let ii : Fin s.card := s.equivFin ⟨i, hi⟩
    let jj : Fin s.card := s.equivFin ⟨j, hj⟩
    have hii : competitorIndex s ii = i := by
      simp [ii, competitorIndex, competitorIndexEquiv]
    have hjj : competitorIndex s jj = j := by
      simp [jj, competitorIndex, competitorIndexEquiv]
    have hij' : ii ≠ jj := by
      intro heq
      apply hij
      rw [← hii, ← hjj, heq]
    have hconverted := h ii jj hij'
    rw [competitorPlainTubeFamily_tube, competitorPlainTubeFamily_tube,
      competitorTube_essentiallyDistinct_iff, hii, hjj] at hconverted
    exact hconverted
  · intro h i j hij
    have hsource_ne : competitorIndex s i ≠ competitorIndex s j := by
      intro heq
      apply hij
      apply (competitorIndexEquiv s).injective
      exact Subtype.ext heq
    rw [competitorPlainTubeFamily_tube, competitorPlainTubeFamily_tube,
      competitorTube_essentiallyDistinct_iff]
    exact h (competitorIndex_mem s i)
      (competitorIndex_mem s j) hsource_ne

/-- The exact competitor shading on the canonical WZ2 enumeration. -/
def competitorTubeShading {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    Kakeya.Streamlined.TubeShading (competitorTubeFamily s V) where
  carrier i := (V (competitorIndex s i)).shade
  measurable_carrier i := (V (competitorIndex s i)).measurableSet_shade
  subset_body i := by
    change (V (competitorIndex s i)).shade ⊆
      ((competitorTubeFamily s V).tube i).carrier
    rw [competitorTubeFamily_carrier]
    exact (V (competitorIndex s i)).shade_subset

@[simp] theorem competitorTubeShading_carrier {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) (i : Fin s.card) :
    (competitorTubeShading s V).carrier i =
      (V (competitorIndex s i)).shade := rfl

theorem competitorTubeShading_union {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    (competitorTubeShading s V).union =
      ⋃ i ∈ s, (V i).shade := by
  ext x
  constructor
  · rintro ⟨i, hi⟩
    refine Set.mem_iUnion₂.mpr
      ⟨competitorIndex s i, competitorIndex_mem s i, ?_⟩
    exact hi
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    let source : s := ⟨i, hi⟩
    let index : Fin s.card := s.equivFin source
    refine ⟨index, ?_⟩
    simpa [index, source, competitorIndex, competitorIndexEquiv] using hxi

theorem competitorTubeShading_mass {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    (competitorTubeShading s V).mass =
      ∑ i ∈ s, volume (V i).shade := by
  rw [Kakeya.Streamlined.Shading.mass]
  exact
    (Fintype.sum_equiv s.equivFin.symm
      (fun i : Fin s.card => volume (V (competitorIndex s i)).shade)
      (fun i : s => volume (V i.1).shade)
      (fun _ => rfl)).trans
      (Finset.sum_coe_sort s fun i => volume (V i).shade)

theorem competitorTubeFamily_mass {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    (competitorTubeFamily s V).toBodyFamily.mass =
      ∑ i ∈ s, volume (V i).carrier := by
  rw [Kakeya.Streamlined.BodyFamily.mass]
  calc
    (∑ i : Fin s.card,
        ((competitorTubeFamily s V).toBodyFamily.body i).volume) =
        ∑ i : Fin s.card, volume (V (competitorIndex s i)).carrier := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Kakeya.Streamlined.TubeFamily.toBodyFamily,
            Kakeya.Streamlined.tubeBody, Kakeya.Streamlined.Body.volume]
    _ = ∑ i : s, volume (V i.1).carrier :=
      Fintype.sum_equiv s.equivFin.symm
        (fun i : Fin s.card => volume (V (competitorIndex s i)).carrier)
        (fun i : s => volume (V i.1).carrier)
        (fun _ => rfl)
    _ = ∑ i ∈ s, volume (V i).carrier :=
      Finset.sum_coe_sort s fun i => volume (V i).carrier

/-- Fixed-radius support is preserved exactly by the canonical enumeration.
The radius remains a parameter so later consumers can specialize it only at
the final `PureWZ2FixedSupportDilatedStickyContract` call. -/
theorem competitorTubeFamily_fixedBallSupport_iff {δ : NNReal}
    (s : Finset ι) (V : ι → ShadedTube δ Space3) (radius : ℝ) :
    Kakeya.Assouad.PureWZ2FixedBallSupport
        (competitorTubeFamily s V) radius ↔
      ∀ i ∈ s, (V i).carrier ⊆
        Metric.closedBall (0 : Space3) radius := by
  constructor
  · intro h i hi
    let source : s := ⟨i, hi⟩
    let index : Fin s.card := s.equivFin source
    have hindex := h index
    simpa [index, source, competitorIndex, competitorIndexEquiv,
      competitorTubeFamily_carrier] using hindex
  · intro h index
    simpa [competitorTubeFamily_carrier] using
      h (competitorIndex s index) (competitorIndex_mem s index)

/-- In particular, the competitor unit-ball premise is exactly WZ2's indexed
`TubeFamily.IsInUnitBall` premise. -/
theorem competitorTubeFamily_isInUnitBall_iff {δ : NNReal}
    (s : Finset ι) (V : ι → ShadedTube δ Space3) :
    (competitorTubeFamily s V).IsInUnitBall ↔
      ∀ i ∈ s, (V i).carrier ⊆
        Metric.closedBall (0 : Space3) 1 := by
  change Kakeya.Assouad.PureWZ2FixedBallSupport
      (competitorTubeFamily s V) 1 ↔ _
  exact competitorTubeFamily_fixedBallSupport_iff s V 1

/-- The competitor quotient fullness is the quotient form of the WZ2
aggregate density on the exact converted family and shading. -/
theorem competitorFullness_eq {δ : NNReal} (s : Finset ι)
    (V : ι → ShadedTube δ Space3) :
    ShadedBody.fullness' s (fun i => (V i).toShadedBody) =
      (competitorTubeShading s V).mass /
        (competitorTubeFamily s V).toBodyFamily.mass := by
  rw [competitorTubeShading_mass, competitorTubeFamily_mass]

/-- On a nonempty positive-radius family, the competitor quotient fullness
inequality and the WZ2 multiplication-form density predicate are equivalent.
The hypotheses establish that the common denominator is nonzero and finite. -/
theorem competitorFullness_le_iff_isLambdaDense {δ : NNReal}
    (hδ0 : 0 < δ) {s : Finset ι} (hs : s.Nonempty)
    (V : ι → ShadedTube δ Space3) (lambda : ENNReal) :
    lambda ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody) ↔
      (competitorTubeShading s V).IsLambdaDense lambda := by
  have hmass_pos : 0 < (competitorTubeFamily s V).toBodyFamily.mass := by
    rw [competitorTubeFamily_mass]
    exact ENNReal.sum_pos_of_nonempty hs fun i _ => by
      let n := Module.finrank ℝ Space3
      have hc0 : (Tube.le_volume.c n : ENNReal) ≠ 0 :=
        (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos n)).ne'
      have hδe0 : (δ : ENNReal) ≠ 0 :=
        (ENNReal.coe_pos.mpr hδ0).ne'
      have hpow0 : (δ : ENNReal) ^ (n - 1) ≠ 0 :=
        pow_ne_zero (n - 1) hδe0
      exact lt_of_lt_of_le
        (pos_iff_ne_zero.mpr (mul_ne_zero hc0 hpow0))
        (Tube.le_volume (V i).toTube)
  have hmass_ne_top :
      (competitorTubeFamily s V).toBodyFamily.mass ≠ ⊤ := by
    rw [competitorTubeFamily_mass]
    exact ENNReal.sum_ne_top.mpr fun i _ =>
      (V i).toTube.isCompact.measure_lt_top.ne
  rw [competitorFullness_eq, Kakeya.Streamlined.Shading.IsLambdaDense,
    ENNReal.le_div_iff_mul_le (Or.inl hmass_pos.ne')
      (Or.inl hmass_ne_top)]

/-- The quotient convention assigns fullness zero to the empty family. -/
@[simp] theorem competitorFullness_empty {δ : NNReal}
    (V : ι → ShadedTube δ Space3) :
    ShadedBody.fullness' (∅ : Finset ι)
      (fun i => (V i).toShadedBody) = 0 := by
  simp [ShadedBody.fullness']

/-- In contrast, the multiplication-form WZ2 density predicate is vacuous on
the empty family.  This is why the preceding equivalence requires nonemptiness. -/
@[simp] theorem competitorTubeShading_isLambdaDense_empty {δ : NNReal}
    (V : ι → ShadedTube δ Space3) (lambda : ENNReal) :
    (competitorTubeShading (∅ : Finset ι) V).IsLambdaDense lambda := by
  simp [Kakeya.Streamlined.Shading.IsLambdaDense,
    competitorTubeFamily_mass, competitorTubeShading_mass]

end FiniteFamily

end Kakeya.Integration

end
