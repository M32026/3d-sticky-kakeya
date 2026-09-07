import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBalancedDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelativeDyadicBandSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransverseFromBalancedCover

/-!
# Relative multiplicity regularization of the sparse direction branch

The high-multiplicity split reserves the margin `24 R <= m`.  A dyadic band
selected only above the floor `m` has new lower multiplicity `M` satisfying
`m < 2 M`; hence `12 R <= M`.  The relative band also preserves the sparse
close-count bound and loses only
`log₂ #family - log₂ m + 1` in shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- The quantitative sparse input after one relative dyadic band. -/
structure SparseRelativeBandPreparationData
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambient : WZ1PaperTubeShading family)
    (densityPower : ENNReal) where
  source : WZ1PaperTubeShading family
  shading : WZ1PaperTubeShading family
  source_subshading : PaperIsSubshading source ambient
  subshading : PaperIsSubshading shading source
  cubical : WZ1PaperIsCubicalShading shading
  originalMultiplicity : ℕ
  closeThreshold : ℕ
  originalMultiplicity_pos : 0 < originalMultiplicity
  closeThreshold_pos : 0 < closeThreshold
  original_density :
    densityPower * family.enncard <= (originalMultiplicity : ENNReal)
  original_budget : 24 * closeThreshold ≤ originalMultiplicity
  original_upper_budget : originalMultiplicity ≤ 48 * closeThreshold
  level : ℕ
  multiplicity : ℕ := 2 ^ level
  multiplicity_eq : multiplicity = 2 ^ level
  level_floor : Nat.log 2 originalMultiplicity ≤ level
  multiplicity_lower : ∀ point ∈ shading.union,
    multiplicity ≤ shading.pointMultiplicity point
  multiplicity_upper : ∀ point ∈ shading.union,
    shading.pointMultiplicity point < 2 * multiplicity
  combinatorial_budget : 12 * closeThreshold ≤ multiplicity
  close_count : ∀ point ∈ shading.union, ∀ index,
    point ∈ shading.carrier index →
    paperCloseDirectionCount shading point index kappa < closeThreshold
  density_lower :
    (densityPower / 2) * family.enncard ≤ (multiplicity : ENNReal)
  coordination_density :
    (densityPower / 24) * family.enncard ≤ (2 * closeThreshold : ℕ)
  bandCount : ℕ :=
    Nat.log 2 family.card - Nat.log 2 originalMultiplicity + 1
  bandCount_eq : bandCount =
    Nat.log 2 family.card - Nat.log 2 originalMultiplicity + 1
  mass_retention :
    (1 / 4 : ENNReal) * ambient.mass ≤
      (bandCount : ENNReal) * shading.mass

namespace SparseRelativeBandPreparationData

/-- Cancel the relative-band loss in the CV absorption budget. -/
theorem absorb_of_ambient_budget
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {densityPower coefficient threshold : ENNReal}
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient densityPower)
    (hbandCountPos : 0 < prepared.bandCount)
    (hambient :
      (prepared.bandCount : ENNReal) * coefficient ≤
        threshold * ((1 / 4 : ENNReal) * ambient.mass)) :
    coefficient ≤ threshold * prepared.shading.mass := by
  have hscaledMass := mul_le_mul_left' prepared.mass_retention threshold
  have hchain : (prepared.bandCount : ENNReal) * coefficient ≤
      (prepared.bandCount : ENNReal) *
        (threshold * prepared.shading.mass) := by
    calc
      (prepared.bandCount : ENNReal) * coefficient ≤
          threshold * ((1 / 4 : ENNReal) * ambient.mass) := hambient
      _ ≤ threshold *
          ((prepared.bandCount : ENNReal) * prepared.shading.mass) :=
        hscaledMass
      _ = (prepared.bandCount : ENNReal) *
          (threshold * prepared.shading.mass) := by ring
  have hbandZero : (prepared.bandCount : ENNReal) ≠ 0 := by
    exact_mod_cast hbandCountPos.ne'
  have hbandTop : (prepared.bandCount : ENNReal) ≠ ⊤ := by simp
  exact (ENNReal.mul_le_mul_iff_right hbandZero hbandTop).mp hchain

end SparseRelativeBandPreparationData

/-- Regularize the sparse branch in a multiplicity band while retaining the
reserved transverse-triple margin. -/
theorem sparse_relative_band_preparation
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient sparse : WZ1PaperTubeShading family}
    (densityPower : ENNReal)
    (m R : ℕ)
    (hm : 0 < m)
    (hR : 0 < R)
    (hbudget : 24 * R ≤ m)
    (hupperBudget : m ≤ 48 * R)
    (hsub : PaperIsSubshading sparse ambient)
    (hcubical : WZ1PaperIsCubicalShading sparse)
    (hmultiplicity : ∀ point ∈ sparse.union,
      m ≤ sparse.pointMultiplicity point)
    (hclose : ∀ point ∈ sparse.union, ∀ index,
      point ∈ sparse.carrier index →
      paperCloseDirectionCount sparse point index kappa < R)
    (hdensity : densityPower * family.enncard ≤ (m : ENNReal))
    (hmass : (1 / 4 : ENNReal) * ambient.mass ≤ sparse.mass) :
    Nonempty (SparseRelativeBandPreparationData
      (kappa := kappa) ambient densityPower) := by
  rcases exists_relative_dyadic_band_with_mass_retention
      hcubical m hm hmultiplicity with
    ⟨level, hlevelFloor, hbandCubical, hbandMultiplicity, hbandMass⟩
  let band := wz1PaperDyadicBandSubshading sparse level
  let M : ℕ := 2 ^ level
  let bandCount : ℕ :=
    Nat.log 2 family.card - Nat.log 2 m + 1
  have hbandSub : PaperIsSubshading band sparse :=
    wz1PaperDyadicBandSubshading_isSubshading sparse level
  have hMlower : ∀ point ∈ band.union,
      M ≤ band.pointMultiplicity point := by
    intro point hpoint
    exact (hbandMultiplicity point hpoint).1
  have hMupper : ∀ point ∈ band.union,
      band.pointMultiplicity point < 2 * M := by
    intro point hpoint
    have hupper := (hbandMultiplicity point hpoint).2
    simpa [M, pow_succ, mul_comm] using hupper
  have hbasePower : 2 ^ Nat.log 2 m ≤ M := by
    dsimp only [M]
    exact Nat.pow_le_pow_right (by norm_num) hlevelFloor
  have hmTwiceBase : m < 2 * 2 ^ Nat.log 2 m := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    simpa [pow_succ, mul_comm] using h
  have hmTwiceM : m < 2 * M := by
    omega
  have hcombinatorial : 12 * R ≤ M := by
    omega
  have hcloseBand : ∀ point ∈ band.union, ∀ index,
      point ∈ band.carrier index →
      paperCloseDirectionCount band point index kappa < R := by
    intro point hpoint index hindex
    have hpointSparse : point ∈ sparse.union :=
      ⟨index, hbandSub index hindex⟩
    exact (close_count_subshading hbandSub).trans_lt
      (hclose point hpointSparse index (hbandSub index hindex))
  have hdensityTwo : densityPower * family.enncard ≤
      (2 : ENNReal) * (M : ENNReal) := by
    calc
      densityPower * family.enncard ≤ (m : ENNReal) := hdensity
      _ ≤ (2 * M : ℕ) := by exact_mod_cast hmTwiceM.le
      _ = (2 : ENNReal) * (M : ENNReal) := by norm_cast
  have hdensityHalf : (densityPower / 2) * family.enncard ≤
      (M : ENNReal) := by
    have hscaled := mul_le_mul_left' hdensityTwo (2 : ENNReal)⁻¹
    have hcancel : (2 : ENNReal)⁻¹ * 2 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    calc
      (densityPower / 2) * family.enncard =
          (2 : ENNReal)⁻¹ *
            (densityPower * family.enncard) := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (2 : ENNReal)⁻¹ *
          ((2 : ENNReal) * (M : ENNReal)) := hscaled
      _ = (M : ENNReal) := by rw [← mul_assoc, hcancel, one_mul]
  have hcoordinationDensity : (densityPower / 24) * family.enncard ≤
      (2 * R : ℕ) := by
    have hdiv : (densityPower / 24) * family.enncard ≤
        (m : ENNReal) / 24 := by
      calc
        (densityPower / 24) * family.enncard =
            (densityPower * family.enncard) / 24 := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ (m : ENNReal) / 24 := by gcongr
    have hmR : (m : ENNReal) / 24 ≤ (2 * R : ℕ) := by
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      have hnat : m ≤ (2 * R) * 24 := by omega
      exact_mod_cast hnat
    exact hdiv.trans hmR
  have hmassFinal : (1 / 4 : ENNReal) * ambient.mass ≤
      (bandCount : ENNReal) * band.mass := by
    exact hmass.trans <| by
      simpa [bandCount, band] using hbandMass
  exact ⟨{
    source := sparse
    shading := band
    source_subshading := hsub
    subshading := hbandSub
    cubical := hbandCubical
    originalMultiplicity := m
    closeThreshold := R
    originalMultiplicity_pos := hm
    closeThreshold_pos := hR
    original_density := hdensity
    original_budget := hbudget
    original_upper_budget := hupperBudget
    level := level
    multiplicity_eq := rfl
    level_floor := hlevelFloor
    multiplicity_lower := hMlower
    multiplicity_upper := hMupper
    combinatorial_budget := hcombinatorial
    close_count := hcloseBand
    density_lower := hdensityHalf
    coordination_density := hcoordinationDensity
    bandCount_eq := rfl
    mass_retention := hmassFinal
  }⟩

end Kakeya.Assouad.PureWZ2

end
