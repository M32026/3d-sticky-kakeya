import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Cubical multiplicity refinement in the literal WZ1 paper model
-/

noncomputable section

namespace Kakeya.Assouad

/-- Literal-paper multiplicity band `[2^level, 2^(level+1))`. -/
def wz1PaperDyadicMultiplicityBand
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (level : ℕ) : Set Point3 :=
  {point |
    ((2 : ℕ) ^ level : ENNReal) ≤
        (shading.pointMultiplicity point : ENNReal) ∧
      (shading.pointMultiplicity point : ENNReal) <
        ((2 : ℕ) ^ (level + 1) : ENNReal)}

theorem wz1PaperDyadicMultiplicityBand_measurable
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (level : ℕ) :
    MeasurableSet
      (wz1PaperDyadicMultiplicityBand shading level) := by
  let allowed : Set ℕ :=
    {multiplicity |
      ((2 : ℕ) ^ level : ENNReal) ≤
          (multiplicity : ENNReal) ∧
        (multiplicity : ENNReal) <
          ((2 : ℕ) ^ (level + 1) : ENNReal)}
  change
    MeasurableSet
      (shading.pointMultiplicity ⁻¹' allowed)
  exact
    MeasurableSet.preimage MeasurableSet.of_discrete
      (measurable_pointMultiplicity shading)

/-- Restrict a paper shading to one dyadic multiplicity band. -/
def wz1PaperDyadicBandSubshading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (level : ℕ) :
    WZ1PaperTubeShading family where
  carrier index :=
    shading.carrier index ∩
      wz1PaperDyadicMultiplicityBand shading level
  measurable_carrier index :=
    (shading.measurable_carrier index).inter
      (wz1PaperDyadicMultiplicityBand_measurable
        shading level)
  subset_body index :=
    Set.inter_subset_left.trans
      (shading.subset_body index)

theorem wz1PaperDyadicBandSubshading_isSubshading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (level : ℕ) :
    ∀ index,
      (wz1PaperDyadicBandSubshading
        shading level).carrier index ⊆
          shading.carrier index :=
  fun _ => Set.inter_subset_left

theorem WZ1PaperIsCubicalShading.carrier_mem_iff_of_same_cell
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (index : Fin family.card)
    {first second : Point3}
    (hsame :
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second) :
    first ∈ shading.carrier index ↔
      second ∈ shading.carrier index := by
  constructor
  · intro hfirst
    apply hcubical index first hfirst
    exact
      (mem_wz1PaperGridCube _ _ _).mpr hsame.symm
  · intro hsecond
    apply hcubical index second hsecond
    exact
      (mem_wz1PaperGridCube _ _ _).mpr hsame

theorem WZ1PaperIsCubicalShading.pointMultiplicity_eq_of_same_cell
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    {first second : Point3}
    (hsame :
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second) :
    shading.pointMultiplicity first =
      shading.pointMultiplicity second := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro index _
  exact
    hcubical.carrier_mem_iff_of_same_cell index hsame

theorem WZ1PaperIsCubicalShading.dyadicBand_mem_iff_of_same_cell
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (level : ℕ)
    {first second : Point3}
    (hsame :
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second) :
    first ∈ wz1PaperDyadicMultiplicityBand shading level ↔
      second ∈ wz1PaperDyadicMultiplicityBand shading level := by
  have hmultiplicity :=
    hcubical.pointMultiplicity_eq_of_same_cell hsame
  simp only [wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq]
  rw [hmultiplicity]

theorem WZ1PaperIsCubicalShading.dyadicBandSubshading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (level : ℕ) :
    WZ1PaperIsCubicalShading
      (wz1PaperDyadicBandSubshading shading level) := by
  intro index first hfirst second hsecond
  rcases hfirst with ⟨hfirstCarrier, hfirstBand⟩
  have hsame :
      wz1PaperGridIndex delta second =
        wz1PaperGridIndex delta first :=
    (mem_wz1PaperGridCube _ _ _).mp hsecond
  have hsecondCarrier :
      second ∈ shading.carrier index :=
    (hcubical.carrier_mem_iff_of_same_cell
      index hsame.symm).mp hfirstCarrier
  have hsecondBand :
      second ∈
        wz1PaperDyadicMultiplicityBand shading level :=
    (hcubical.dyadicBand_mem_iff_of_same_cell
      level hsame.symm).mp hfirstBand
  exact ⟨hsecondCarrier, hsecondBand⟩

end Kakeya.Assouad
