import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData

/-!
# Cubical point-multiplicity refinement inside a large-slope slab

Paper Section 6 first restricts attention to the selected horizontal slab and
then pigeonholes the point multiplicity.  Intersecting a paper shading with an
arbitrary slab can cut literal `delta`-cells, so the refinement here instead
selects among the global cubical dyadic bands using their mass *inside* the
slab.  This preserves whole cells and still retains the required logarithmic
fraction of the slab mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/--
A whole-cell dyadic multiplicity band selected according to its mass in one
horizontal slab.
-/
structure LargeSlopeCroppedMultiplicityBandData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (a b : ℝ) where
  level : ℕ
  band : WZ1PaperTubeShading family
  band_eq :
    band = wz1PaperDyadicBandSubshading shading level
  band_cubical : WZ1PaperIsCubicalShading band
  band_subshading :
    ∀ index, band.carrier index ⊆ shading.carrier index
  slab_mass_retention :
    paperShadedMassInSlab shading a b /
          ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≤
      paperShadedMassInSlab band a b
  band_multiplicity :
    ∀ point ∈ band.union,
      (2 ^ level : ENNReal) ≤
          (band.pointMultiplicity point : ENNReal) ∧
        (band.pointMultiplicity point : ENNReal) <
          (2 ^ (level + 1) : ENNReal)

/-- A selected dyadic paper band has the standard constant-multiplicity form. -/
theorem LargeSlopeCroppedMultiplicityBandData.hasConstantMultiplicity
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {a b : ℝ}
    (data : LargeSlopeCroppedMultiplicityBandData shading a b) :
    data.band.HasConstantMultiplicity
      (2 ^ data.level) (2 * 2 ^ data.level) := by
  intro point hpoint
  have hband := data.band_multiplicity point hpoint
  constructor
  · exact_mod_cast hband.1
  · have hupper :
        data.band.pointMultiplicity point < 2 ^ (data.level + 1) := by
      exact_mod_cast hband.2
    have hpow : 2 ^ (data.level + 1) = 2 * 2 ^ data.level := by
      rw [pow_succ]
      ring
    rw [hpow] at hupper
    exact hupper.le

/--
The slab incidence mass of a dyadic band is at most its upper multiplicity
times the three-dimensional volume of the band union inside the slab.
-/
theorem LargeSlopeCroppedMultiplicityBandData.slabMass_le_mul_volume
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {a b : ℝ}
    (data : LargeSlopeCroppedMultiplicityBandData shading a b) :
    paperShadedMassInSlab data.band a b ≤
      (2 * 2 ^ data.level : ℕ) *
        volume (data.band.union ∩ horizontalSlab a b) := by
  let slabBand : WZ1PaperTubeShading family :=
    { carrier := fun index =>
        data.band.carrier index ∩ horizontalSlab a b
      measurable_carrier := fun index =>
        (data.band.measurable_carrier index).inter
          (measurableSet_horizontalSlab a b)
      subset_body := fun index =>
        Set.inter_subset_left.trans (data.band.subset_body index) }
  have hunion :
      slabBand.union = data.band.union ∩ horizontalSlab a b := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, hpoint⟩, hslab⟩
      exact ⟨index, hpoint, hslab⟩
  have hmultiplicity :
      ∀ point ∈ slabBand.union,
        slabBand.pointMultiplicity point =
          data.band.pointMultiplicity point := by
    intro point hpoint
    have hslab : point ∈ horizontalSlab a b := by
      rw [hunion] at hpoint
      exact hpoint.2
    classical
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    ext index
    simp [slabBand, hslab]
  have hconstant :
      slabBand.HasConstantMultiplicity
        (2 ^ data.level) (2 * 2 ^ data.level) := by
    intro point hpoint
    have hband : point ∈ data.band.union := by
      rw [hunion] at hpoint
      exact hpoint.1
    rw [hmultiplicity point hpoint]
    exact data.hasConstantMultiplicity point hband
  have hmass :
      slabBand.mass = paperShadedMassInSlab data.band a b := by
    rfl
  have hbound :=
    (constant_multiplicity_mass_volume_generic hconstant).2
  rw [hmass, hunion] at hbound
  simpa [Nat.cast_mul] using hbound

/-- Quantitative union-volume floor obtained from the retained slab mass. -/
theorem LargeSlopeCroppedMultiplicityBandData.slabUnionVolume_lower
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {a b : ℝ}
    (data : LargeSlopeCroppedMultiplicityBandData shading a b) :
    paperShadedMassInSlab shading a b /
          ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) /
          (2 * 2 ^ data.level : ℕ) ≤
      volume (data.band.union ∩ horizontalSlab a b) := by
  let cap : ENNReal := (2 * 2 ^ data.level : ℕ)
  have hcap_zero : cap ≠ 0 := by
    simp [cap]
  have hcap_top : cap ≠ ⊤ := by
    dsimp only [cap]
    exact ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hcap_zero hcap_top]
  simpa [cap, mul_comm] using
    data.slab_mass_retention.trans data.slabMass_le_mul_volume

/-- Positive retained slab incidence forces positive band-union volume. -/
theorem LargeSlopeCroppedMultiplicityBandData.slabUnionVolume_ne_zero
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {a b : ℝ}
    (data : LargeSlopeCroppedMultiplicityBandData shading a b)
    (hslabMass : paperShadedMassInSlab shading a b ≠ 0) :
    volume (data.band.union ∩ horizontalSlab a b) ≠ 0 := by
  have hlevels :
      (((Nat.log 2 family.card + 1 : ℕ) : ENNReal)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero (Nat.log 2 family.card))
  have hretained : paperShadedMassInSlab data.band a b ≠ 0 := by
    intro hzero
    have hdivZero :
        paperShadedMassInSlab shading a b /
            ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) = 0 := by
      exact le_zero_iff.mp (data.slab_mass_retention.trans_eq hzero)
    have hdenTop :
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≠ ⊤ := by simp
    have hsourceZero : paperShadedMassInSlab shading a b = 0 := by
      exact ((ENNReal.div_eq_zero_iff).mp hdivZero).resolve_right hdenTop
    exact hslabMass hsourceZero
  intro hunionZero
  have hmassZero : paperShadedMassInSlab data.band a b = 0 := by
    apply le_zero_iff.mp
    calc
      paperShadedMassInSlab data.band a b
          ≤ (2 * 2 ^ data.level : ℕ) *
              volume (data.band.union ∩ horizontalSlab a b) :=
        data.slabMass_le_mul_volume
      _ = 0 := by rw [hunionZero, mul_zero]
  exact hretained hmassZero

private lemma croppedBand_disjoint_of_lt
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {first second : ℕ}
    (hlt : first < second) :
    Disjoint
      (wz1PaperDyadicMultiplicityBand shading first)
      (wz1PaperDyadicMultiplicityBand shading second) := by
  apply Set.disjoint_left.mpr
  intro point hfirst hsecond
  have hlevels : first + 1 ≤ second := by omega
  have hpowers :
      (2 ^ (first + 1) : ENNReal) ≤
        (2 ^ second : ENNReal) := by
    exact_mod_cast
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hlevels
  exact
    (not_le_of_gt hfirst.2)
      (hpowers.trans hsecond.1)

private lemma croppedBand_disjoint
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {first second : ℕ}
    (hne : first ≠ second) :
    Disjoint
      (wz1PaperDyadicMultiplicityBand shading first)
      (wz1PaperDyadicMultiplicityBand shading second) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact croppedBand_disjoint_of_lt hlt
  · exact (croppedBand_disjoint_of_lt hgt).symm

private lemma point_mem_croppedDyadicBand
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {index : Fin family.card}
    {point : Point3}
    (hpoint : point ∈ shading.carrier index) :
    ∃ level ∈ Finset.range (Nat.log 2 family.card + 1),
      point ∈ wz1PaperDyadicMultiplicityBand shading level := by
  let multiplicity := shading.pointMultiplicity point
  have hindex :
      index ∈
        Finset.univ.filter fun candidate : Fin family.card =>
          point ∈ shading.carrier candidate := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpoint
  have hmultiplicity_pos : 0 < multiplicity := by
    exact Finset.card_pos.mpr ⟨index, hindex⟩
  have hmultiplicity_le : multiplicity ≤ family.card := by
    change
      (Finset.univ.filter
        (fun candidate : Fin family.card =>
          point ∈ shading.carrier candidate)).card ≤
        family.card
    have hsubset :
        Finset.univ.filter
            (fun candidate : Fin family.card =>
              point ∈ shading.carrier candidate) ⊆
          (Finset.univ : Finset (Fin family.card)) :=
      Finset.filter_subset _ _
    simpa using Finset.card_le_card hsubset
  let level := Nat.log 2 multiplicity
  have hlower :
      (2 : ℕ) ^ level ≤ multiplicity :=
    Nat.pow_log_le_self 2 hmultiplicity_pos.ne'
  have hupper :
      multiplicity < (2 : ℕ) ^ (level + 1) := by
    apply Nat.lt_pow_of_log_lt (by norm_num)
    simp [level]
  have hlevel : level < Nat.log 2 family.card + 1 := by
    have hlog :
        Nat.log 2 multiplicity ≤ Nat.log 2 family.card :=
      Nat.log_mono_right hmultiplicity_le
    omega
  refine ⟨level, Finset.mem_range.mpr hlevel, ?_⟩
  constructor
  · exact_mod_cast hlower
  · exact_mod_cast hupper

private lemma croppedDyadicBands_partition_in_slab
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (a b : ℝ)
    (index : Fin family.card) :
    shading.carrier index ∩ horizontalSlab a b =
      ⋃ level ∈ Finset.range (Nat.log 2 family.card + 1),
        (wz1PaperDyadicBandSubshading shading level).carrier index ∩
          horizontalSlab a b := by
  ext point
  constructor
  · intro hpoint
    rcases point_mem_croppedDyadicBand hpoint.1 with
      ⟨level, hlevel, hband⟩
    exact
      Set.mem_iUnion.mpr
        ⟨level, Set.mem_iUnion.mpr
          ⟨hlevel, ⟨⟨hpoint.1, hband⟩, hpoint.2⟩⟩⟩
  · intro hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨level, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨_, hpoint⟩
    exact ⟨hpoint.1.1, hpoint.2⟩

/--
The slab mass is the sum of the slab masses of all global cubical dyadic
point-multiplicity bands.
-/
theorem paperDyadicBands_slabMass_sum
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (a b : ℝ) :
    paperShadedMassInSlab shading a b =
      ∑ level ∈ Finset.range (Nat.log 2 family.card + 1),
        paperShadedMassInSlab
          (wz1PaperDyadicBandSubshading shading level) a b := by
  let levels := Finset.range (Nat.log 2 family.card + 1)
  have hcarrier :
      ∀ index : Fin family.card,
        volume (shading.carrier index ∩ horizontalSlab a b) =
          ∑ level ∈ levels,
            volume
              ((wz1PaperDyadicBandSubshading shading level).carrier index ∩
                horizontalSlab a b) := by
    intro index
    let pieces : ℕ → Set Point3 :=
      fun level =>
        (wz1PaperDyadicBandSubshading shading level).carrier index ∩
          horizontalSlab a b
    have hdisjoint :
        (levels : Set ℕ).PairwiseDisjoint pieces := by
      intro first _ second _ hne
      exact
        (croppedBand_disjoint hne).mono
          (Set.inter_subset_left.trans Set.inter_subset_right)
          (Set.inter_subset_left.trans Set.inter_subset_right)
    have hmeasurable :
        ∀ level ∈ levels, MeasurableSet (pieces level) := by
      intro level _
      exact
        ((wz1PaperDyadicBandSubshading shading level).measurable_carrier
          index).inter (measurableSet_horizontalSlab a b)
    have hpartition :
        shading.carrier index ∩ horizontalSlab a b =
          ⋃ level ∈ levels, pieces level := by
      simpa [levels, pieces] using
        croppedDyadicBands_partition_in_slab
          (shading := shading) a b index
    calc
      volume (shading.carrier index ∩ horizontalSlab a b) =
          volume (⋃ level ∈ levels, pieces level) := by
        rw [hpartition]
      _ = ∑ level ∈ levels, volume (pieces level) :=
        MeasureTheory.measure_biUnion_finset
          hdisjoint hmeasurable
  calc
    paperShadedMassInSlab shading a b =
        ∑ index : Fin family.card,
          volume (shading.carrier index ∩ horizontalSlab a b) := rfl
    _ =
        ∑ index : Fin family.card,
          ∑ level ∈ levels,
            volume
              ((wz1PaperDyadicBandSubshading shading level).carrier index ∩
                horizontalSlab a b) := by
      apply Finset.sum_congr rfl
      intro index _
      exact hcarrier index
    _ =
        ∑ level ∈ levels,
          ∑ index : Fin family.card,
            volume
              ((wz1PaperDyadicBandSubshading shading level).carrier index ∩
                horizontalSlab a b) := by
      rw [Finset.sum_comm]
    _ =
        ∑ level ∈ levels,
          paperShadedMassInSlab
            (wz1PaperDyadicBandSubshading shading level) a b := by
      rfl

/-- The point-multiplicity bands partition the union spatially. -/
theorem paperDyadicBands_unionVolume_sum
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    volume shading.union =
      ∑ level ∈ Finset.range (Nat.log 2 family.card + 1),
        volume (wz1PaperDyadicBandSubshading shading level).union := by
  let levels := Finset.range (Nat.log 2 family.card + 1)
  have hpartition : shading.union = ⋃ level ∈ levels,
      (wz1PaperDyadicBandSubshading shading level).union := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      rcases point_mem_croppedDyadicBand hpoint with
        ⟨level, hlevel, hband⟩
      exact Set.mem_iUnion₂.mpr
        ⟨level, hlevel, ⟨index, hpoint, hband⟩⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨_level, _hlevel, index, hpoint⟩
      exact ⟨index, hpoint.1⟩
  have hdisjoint : Set.PairwiseDisjoint (levels : Set ℕ) fun level =>
      (wz1PaperDyadicBandSubshading shading level).union := by
    intro first _ second _ hne
    apply Set.disjoint_left.mpr
    intro point hfirst hsecond
    rcases hfirst with ⟨_firstIndex, hfirstCarrier⟩
    rcases hsecond with ⟨_secondIndex, hsecondCarrier⟩
    exact Set.disjoint_left.mp (croppedBand_disjoint hne)
      hfirstCarrier.2 hsecondCarrier.2
  calc
    volume shading.union = volume (⋃ level ∈ levels,
        (wz1PaperDyadicBandSubshading shading level).union) :=
      congrArg volume hpartition
    _ = ∑ level ∈ levels,
        volume (wz1PaperDyadicBandSubshading shading level).union := by
      exact MeasureTheory.measure_biUnion_finset hdisjoint
        (fun level _ =>
          measurableSet_shading_union
            (wz1PaperDyadicBandSubshading shading level))

/-- A whole-cell point-multiplicity band selected by spatial volume. -/
structure LargeSlopeCroppedSpatialMultiplicityBandData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) where
  level : ℕ
  band : WZ1PaperTubeShading family
  band_eq : band = wz1PaperDyadicBandSubshading shading level
  band_cubical : WZ1PaperIsCubicalShading band
  band_subshading : ∀ index, band.carrier index ⊆ shading.carrier index
  volume_retention :
    volume shading.union /
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) ≤
      volume band.union
  band_multiplicity : ∀ point ∈ band.union,
    (2 ^ level : ENNReal) ≤ (band.pointMultiplicity point : ENNReal) ∧
      (band.pointMultiplicity point : ENNReal) <
        (2 ^ (level + 1) : ENNReal)

namespace LargeSlopeCroppedSpatialMultiplicityBandData

theorem hasConstantMultiplicity
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data : LargeSlopeCroppedSpatialMultiplicityBandData shading) :
    data.band.HasConstantMultiplicity
      (2 ^ data.level) (2 * 2 ^ data.level) := by
  intro point hpoint
  have hband := data.band_multiplicity point hpoint
  constructor
  · exact_mod_cast hband.1
  · have hupper : data.band.pointMultiplicity point <
        2 ^ (data.level + 1) := by exact_mod_cast hband.2
    rw [pow_succ] at hupper
    simpa [mul_comm] using hupper.le

theorem mass_lower
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data : LargeSlopeCroppedSpatialMultiplicityBandData shading) :
    (2 ^ data.level : ENNReal) * volume data.band.union ≤
      data.band.mass := by
  simpa using (constant_multiplicity_mass_volume_generic
    data.hasConstantMultiplicity).1

theorem mass_upper
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data : LargeSlopeCroppedSpatialMultiplicityBandData shading) :
    data.band.mass ≤ (2 * 2 ^ data.level : ENNReal) *
      volume data.band.union := by
  simpa using (constant_multiplicity_mass_volume_generic
    data.hasConstantMultiplicity).2

end LargeSlopeCroppedSpatialMultiplicityBandData

/-- Select a whole-cell dyadic band retaining the average spatial volume. -/
theorem largeSlope_cropped_spatialMultiplicityBand
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading) :
    Nonempty (LargeSlopeCroppedSpatialMultiplicityBandData shading) := by
  let levels := Finset.range (Nat.log 2 family.card + 1)
  let bandVolume : ℕ → ENNReal := fun level =>
    volume (wz1PaperDyadicBandSubshading shading level).union
  have hlevels : levels.Nonempty := by simp [levels]
  rcases Finset.exists_max_image levels bandVolume hlevels with
    ⟨level, hlevel, hmax⟩
  have hsum : volume shading.union =
      ∑ candidate ∈ levels, bandVolume candidate := by
    simpa [levels, bandVolume] using paperDyadicBands_unionVolume_sum shading
  have hsumLe : ∑ candidate ∈ levels, bandVolume candidate ≤
      levels.card • bandVolume level :=
    Finset.sum_le_card_nsmul levels bandVolume (bandVolume level) hmax
  have hcard : (levels.card : ENNReal) =
      (Nat.log 2 family.card + 1 : ℕ) := by simp [levels]
  have hcardZero : (levels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hlevels.card_pos.ne'
  have hcardTop : (levels.card : ENNReal) ≠ ⊤ := by simp
  have hvolume : volume shading.union / (levels.card : ENNReal) ≤
      bandVolume level := by
    rw [ENNReal.div_le_iff hcardZero hcardTop, hsum]
    simpa [nsmul_eq_mul, mul_comm] using hsumLe
  exact ⟨{
    level := level
    band := wz1PaperDyadicBandSubshading shading level
    band_eq := rfl
    band_cubical := hcubical.dyadicBandSubshading level
    band_subshading :=
      wz1PaperDyadicBandSubshading_isSubshading shading level
    volume_retention := by simpa [bandVolume, hcard] using hvolume
    band_multiplicity := by
      intro point hpoint
      have hband : point ∈
          wz1PaperDyadicMultiplicityBand shading level := by
        rcases hpoint with ⟨index, hpoint⟩
        exact hpoint.2
      have hmultiplicity :
          (wz1PaperDyadicBandSubshading shading level).pointMultiplicity
              point = shading.pointMultiplicity point := by
        classical
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        congr 1
        apply Finset.filter_congr
        intro index _
        change
          (point ∈ shading.carrier index ∧
              point ∈ wz1PaperDyadicMultiplicityBand shading level) ↔
            point ∈ shading.carrier index
        exact and_iff_left hband
      rw [hmultiplicity]
      exact hband
  }⟩

private theorem croppedDyadicBand_multiplicity
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (level : ℕ) :
    ∀ point ∈
        (wz1PaperDyadicBandSubshading shading level).union,
      (2 ^ level : ENNReal) ≤
          ((wz1PaperDyadicBandSubshading shading level).pointMultiplicity
            point : ENNReal) ∧
        ((wz1PaperDyadicBandSubshading shading level).pointMultiplicity
            point : ENNReal) <
          (2 ^ (level + 1) : ENNReal) := by
  intro point hpoint
  have hband :
      point ∈ wz1PaperDyadicMultiplicityBand shading level := by
    rcases hpoint with ⟨index, hpoint⟩
    exact hpoint.2
  have hmultiplicity :
      (wz1PaperDyadicBandSubshading shading level).pointMultiplicity point =
        shading.pointMultiplicity point := by
    classical
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    change
      (point ∈ shading.carrier index ∧
          point ∈ wz1PaperDyadicMultiplicityBand shading level) ↔
        point ∈ shading.carrier index
    exact and_iff_left hband
  rw [hmultiplicity]
  exact hband

/--
Select a whole-cell dyadic point-multiplicity band retaining a logarithmic
fraction of the source shading's mass inside the specified slab.
-/
theorem largeSlope_cropped_multiplicityBand
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (a b : ℝ) :
    Nonempty (LargeSlopeCroppedMultiplicityBandData shading a b) := by
  let levels := Finset.range (Nat.log 2 family.card + 1)
  let bandMass : ℕ → ENNReal :=
    fun level =>
      paperShadedMassInSlab
        (wz1PaperDyadicBandSubshading shading level) a b
  have hlevels : levels.Nonempty := by
    simp [levels]
  rcases Finset.exists_max_image levels bandMass hlevels with
    ⟨level, hlevel, hmax⟩
  have hsum :
      paperShadedMassInSlab shading a b =
        ∑ candidate ∈ levels, bandMass candidate := by
    simpa [levels, bandMass] using
      paperDyadicBands_slabMass_sum shading a b
  have hsum_le :
      ∑ candidate ∈ levels, bandMass candidate ≤
        levels.card • bandMass level :=
    Finset.sum_le_card_nsmul
      levels bandMass (bandMass level) hmax
  have hcard :
      (levels.card : ENNReal) =
        (Nat.log 2 family.card + 1 : ℕ) := by
    simp [levels]
  have hcard_ne_zero : (levels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hlevels.card_pos.ne'
  have hcard_ne_top : (levels.card : ENNReal) ≠ ⊤ := by
    simp
  have hmass :
      paperShadedMassInSlab shading a b /
          (levels.card : ENNReal) ≤
        bandMass level := by
    rw [ENNReal.div_le_iff hcard_ne_zero hcard_ne_top]
    rw [hsum]
    simpa [nsmul_eq_mul, mul_comm] using hsum_le
  exact
    ⟨{
      level := level
      band := wz1PaperDyadicBandSubshading shading level
      band_eq := rfl
      band_cubical := hcubical.dyadicBandSubshading level
      band_subshading :=
        wz1PaperDyadicBandSubshading_isSubshading shading level
      slab_mass_retention := by
        simpa [bandMass, hcard] using hmass
      band_multiplicity :=
        croppedDyadicBand_multiplicity shading level
    }⟩

end Kakeya.Assouad

end
