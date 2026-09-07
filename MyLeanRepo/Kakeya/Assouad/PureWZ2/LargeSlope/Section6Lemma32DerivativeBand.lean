import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma31Uniform
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.MassSlopeSelection

/-!
# WZ2 Lemma 32 derivative band

The uniform Lemma-31 slab is shortened only enough to put the derivative in
one dyadic bracket.  No spatial transformation is performed in this module.
-/

noncomputable section
namespace Kakeya.Assouad

open Set

structure PureWZ2Lemma32DerivativeBandAssembly
    (sigma epsilon delta : ℝ) where
  lemma31 : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta
  /-- The shading whose mass is used when the derivative interval is chosen.
  The canonical constructor below takes the full Section-6 slab shading; a
  later common-slice refinement may instead take its whole-cell `F2`
  subshading without changing the derivative argument. -/
  sourceShading : WZ1PaperTubeShading lemma31.data.cfg.family
  source_subshading : ∀ index, sourceShading.carrier index ⊆
    lemma31.data.cfg.shading.carrier index
  /-- Loss exponent appearing in the mass floor for `sourceShading`.  This is
  equal to the Lemma-31 loss for the canonical constructor, but may be larger
  after an earlier whole-cell refinement. -/
  massLoss : ℝ
  left : ℝ
  right : ℝ
  slopeScale : ℝ
  left_mem : lemma31.data.scaleData.slabLeft ≤ left
  ordered : left < right
  right_mem : right ≤ lemma31.data.scaleData.slabRight
  length_eq : right - left = lemma31.data.rho.1 / 50
  slopeScale_pos : 0 < slopeScale
  slopeScale_lower : lemma31.data.rho.1 ≤ slopeScale
  slopeScale_le_one : slopeScale ≤ 1
  derivative_band : ∀ z ∈ Set.Icc left right,
    slopeScale ≤
        |deriv lemma31.data.globalSlope z| ∧
      |deriv lemma31.data.globalSlope z| ≤
        2 * slopeScale
  /-- The actual Lipschitz-width estimate from the minimum-derivative
  selection, retained before weakening the upper endpoint to `2m`. -/
  derivative_tight_upper : ∀ z ∈ Set.Icc left right,
    |deriv lemma31.data.globalSlope z| ≤
      slopeScale + lemma31.data.rho.1 / 50
  /-- The selected derivative window retains one fiftieth of the full
  Proposition-5 slab mass.  This card-proportional form is the input needed
  by paper Lemma 8; the weaker scalar floor below is retained for callers
  that do not track source cardinality. -/
  shaded_mass_card :
    ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (massLoss + 2) *
        lemma31.data.cfg.family.enncard *
        ENNReal.ofReal lemma31.data.rho.1 / 50 ≤
      shadedMassInSlab sourceShading left right
  shaded_mass :
    Kakeya.realRpowENN delta (massLoss + 3) *
        ENNReal.ofReal lemma31.data.rho.1 / 50 ≤
      shadedMassInSlab sourceShading left right

theorem PureWZ2Lemma31DerivativeAssembly.toLemma32DerivativeBand
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta) :
    Nonempty (PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) := by
  let slope := data.data.globalSlope
  let left := data.data.scaleData.slabLeft
  let right := data.data.scaleData.slabRight
  let width := data.data.rho.1
  have hleftRight : left < right := data.data.scaleData.slab_ordered
  have hwidth : right - left = width := data.data.scaleData.slab_width
  have hwidthPos : 0 < width := by
    exact data.data.cfg.extremal.delta_pos.trans_le data.data.rho.2.1
  have hinterval : Set.Icc left right ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨data.data.scaleData.slabLeft_mem.trans hz.1,
      hz.2.trans data.data.scaleData.slabRight_mem⟩
  have hlow : ∀ z ∈ Set.Icc left right,
      width ≤ |deriv slope z| := by
    intro z hz
    have h := data.derivative_lower z hz
    rw [data.data.scaleData.slab_width] at h
    simpa [slope] using h
  have hslabMass : Kakeya.realRpowENN delta (data.data.targetLoss + 3) *
      ENNReal.ofReal (right - left) ≤
        shadedMassInSlab data.data.scaleData.slabShading left right := by
    rw [hwidth]
    have hmassEq : shadedMassInSlab data.data.scaleData.slabShading
        left right = data.data.scaleData.slabShading.mass := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Set.inter_eq_left.mpr (data.data.scaleData.slab_in_slab index)]
    rw [hmassEq]
    have hfamilyOne : (1 : ENNReal) ≤ data.data.cfg.family.enncard := by
      change (1 : ENNReal) ≤ (data.data.cfg.family.card : ENNReal)
      exact_mod_cast data.data.cfg.extremal.nonempty
    have hdeltaPi : Kakeya.realRpowENN delta 1 ≤
        ENNReal.ofReal (Real.pi / 4) := by
      have hreal : delta ≤ Real.pi / 4 :=
        data.delta_small.trans (by linarith [Real.pi_gt_three])
      calc
        Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
          simp [Kakeya.realRpowENN]
        _ ≤ ENNReal.ofReal (Real.pi / 4) := ENNReal.ofReal_mono hreal
    have hcoefficient : Kakeya.realRpowENN delta 1 ≤
        ENNReal.ofReal (Real.pi / 4) *
          data.data.cfg.family.enncard := by
      calc
        Kakeya.realRpowENN delta 1 ≤
            ENNReal.ofReal (Real.pi / 4) := hdeltaPi
        _ = ENNReal.ofReal (Real.pi / 4) * 1 := by simp
        _ ≤ ENNReal.ofReal (Real.pi / 4) *
            data.data.cfg.family.enncard := by gcongr
    calc
      Kakeya.realRpowENN delta (data.data.targetLoss + 3) *
            ENNReal.ofReal width =
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            Kakeya.realRpowENN delta 1 * ENNReal.ofReal width := by
              rw [← realRpowENN_add data.data.cfg.extremal.delta_pos]
              congr 2
              ring
      _ ≤
          ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard * ENNReal.ofReal width := by
              calc
                Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
                    Kakeya.realRpowENN delta 1 * ENNReal.ofReal width ≤
                  Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
                    (ENNReal.ofReal (Real.pi / 4) *
                      data.data.cfg.family.enncard) *
                        ENNReal.ofReal width := by gcongr
                _ = _ := by ring
      _ ≤ data.data.scaleData.slabShading.mass := data.data.scaleData.slab_mass
  have hlow' : ∀ z ∈ Set.Icc left right,
      right - left ≤ |deriv slope z| := by
    intro z hz
    rw [hwidth]
    exact hlow z hz
  rcases mass_slope_selection_tight slope
      data.data.globalSlope_normalized hleftRight
      hinterval hlow' data.data.scaleData.slabShading hslabMass with
    ⟨c, d, hc, hcd, hd, hlength,
      ⟨m, hm, hmWidth, hmOne, hband, htight⟩, hmassFraction, hmass⟩
  have hmassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
          data.data.cfg.family.enncard * ENNReal.ofReal width / 50 ≤
        shadedMassInSlab data.data.scaleData.slabShading c d := by
    have hslabEq : shadedMassInSlab data.data.scaleData.slabShading
        left right = data.data.scaleData.slabShading.mass := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Set.inter_eq_left.mpr
        (data.data.scaleData.slab_in_slab index)]
    calc
      ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard * ENNReal.ofReal width / 50 ≤
          data.data.scaleData.slabShading.mass / 50 := by
            exact ENNReal.div_le_div data.data.scaleData.slab_mass
              (by norm_num)
      _ = shadedMassInSlab data.data.scaleData.slabShading left right / 50 := by
            rw [hslabEq]
      _ ≤ shadedMassInSlab data.data.scaleData.slabShading c d :=
            hmassFraction
  exact ⟨{
    lemma31 := data
    sourceShading := data.data.scaleData.slabShading
    source_subshading := data.data.scaleData.slab_subshading
    massLoss := data.data.targetLoss
    left := c
    right := d
    slopeScale := m
    left_mem := hc
    ordered := hcd
    right_mem := hd
    length_eq := by
      calc
        d - c = (right - left) / 50 := hlength
        _ = width / 50 := by rw [hwidth]
    slopeScale_pos := hm
    slopeScale_lower := by
      calc
        width = right - left := hwidth.symm
        _ ≤ m := hmWidth
    slopeScale_le_one := hmOne
    derivative_band := by
      simpa [slope] using hband
    derivative_tight_upper := by
      intro z hz
      have h := htight z hz
      rw [hwidth] at h
      simpa [slope] using h
    shaded_mass_card := hmassCard
    shaded_mass := by
      rw [hwidth] at hmass
      exact hmass
  }⟩

/-- Run the derivative-interval selection on a chosen source refinement.  The
derivative bracket depends only on the common slope, while the two mass fields
record exactly the shading supplied by the caller.  This is the interface used
after the rotated common-y whole-label refinement. -/
theorem PureWZ2Lemma31DerivativeAssembly.toLemma32DerivativeBandOn
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (sourceShading : WZ1PaperTubeShading data.data.cfg.family)
    (massLoss : ℝ)
    (hsourceSub : ∀ index, sourceShading.carrier index ⊆
      data.data.cfg.shading.carrier index)
    (hsourceInSlab : ∀ index, sourceShading.carrier index ⊆
      horizontalSlab data.data.scaleData.slabLeft
        data.data.scaleData.slabRight)
    (hsourceMassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 ≤
        sourceShading.mass)
    (hsourceMass :
      Kakeya.realRpowENN delta (massLoss + 3) *
          ENNReal.ofReal data.data.rho.1 ≤ sourceShading.mass) :
    ∃ band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta,
      band.lemma31 = data ∧ band.sourceShading.union = sourceShading.union ∧
        band.massLoss = massLoss := by
  let slope := data.data.globalSlope
  let left := data.data.scaleData.slabLeft
  let right := data.data.scaleData.slabRight
  let width := data.data.rho.1
  have hleftRight : left < right := data.data.scaleData.slab_ordered
  have hwidth : right - left = width := data.data.scaleData.slab_width
  have hinterval : Set.Icc left right ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨data.data.scaleData.slabLeft_mem.trans hz.1,
      hz.2.trans data.data.scaleData.slabRight_mem⟩
  have hlow : ∀ z ∈ Set.Icc left right,
      right - left ≤ |deriv slope z| := by
    intro z hz
    simpa [slope] using data.derivative_lower z hz
  have hmass : Kakeya.realRpowENN delta (massLoss + 3) *
      ENNReal.ofReal (right - left) ≤
        shadedMassInSlab sourceShading left right := by
    rw [hwidth]
    have hmassEq : shadedMassInSlab sourceShading left right =
        sourceShading.mass := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Set.inter_eq_left.mpr (hsourceInSlab index)]
    rw [hmassEq]
    exact hsourceMass
  rcases mass_slope_selection_tight slope data.data.globalSlope_normalized
      hleftRight hinterval hlow sourceShading hmass with
    ⟨c, d, hc, hcd, hd, hlength,
      ⟨m, hm, hmWidth, hmOne, hband, htight⟩, _hmassFraction, hmass'⟩
  have hmassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard * ENNReal.ofReal width / 50 ≤
        shadedMassInSlab sourceShading c d := by
    have hmassEq : shadedMassInSlab sourceShading left right =
        sourceShading.mass := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Set.inter_eq_left.mpr (hsourceInSlab index)]
    calc
      ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (massLoss + 2) *
            data.data.cfg.family.enncard * ENNReal.ofReal width / 50 ≤
          sourceShading.mass / 50 :=
        ENNReal.div_le_div hsourceMassCard (by norm_num)
      _ = shadedMassInSlab sourceShading left right / 50 := by rw [hmassEq]
      _ ≤ shadedMassInSlab sourceShading c d := _hmassFraction
  refine ⟨{
    lemma31 := data
    sourceShading := sourceShading
    source_subshading := hsourceSub
    massLoss := massLoss
    left := c
    right := d
    slopeScale := m
    left_mem := hc
    ordered := hcd
    right_mem := hd
    length_eq := by simpa [hwidth] using hlength
    slopeScale_pos := hm
    slopeScale_lower := by simpa [hwidth] using hmWidth
    slopeScale_le_one := hmOne
    derivative_band := by
      simpa [slope] using hband
    derivative_tight_upper := by
      simpa [slope, hwidth] using htight
    shaded_mass_card := hmassCard
    shaded_mass := by simpa [hwidth] using hmass'
  }, rfl, rfl, rfl⟩

/-- Repackage a derivative band on a smaller source shading without changing
its interval or slope bracket.  The caller supplies the two quantitative mass
bounds on the smaller shading. -/
def PureWZ2Lemma32DerivativeBandAssembly.restrictSource
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (sourceShading : WZ1PaperTubeShading band.lemma31.data.cfg.family)
    (massLoss : ℝ)
    (hsourceSub : ∀ index, sourceShading.carrier index ⊆
      band.lemma31.data.cfg.shading.carrier index)
    (hsourceMassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          band.lemma31.data.cfg.family.enncard *
          ENNReal.ofReal band.lemma31.data.rho.1 / 50 ≤
        shadedMassInSlab sourceShading band.left band.right)
    (hsourceMass :
      Kakeya.realRpowENN delta (massLoss + 3) *
          ENNReal.ofReal band.lemma31.data.rho.1 / 50 ≤
        shadedMassInSlab sourceShading band.left band.right) :
    PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta :=
  { band with
    sourceShading := sourceShading
    source_subshading := hsourceSub
    massLoss := massLoss
    shaded_mass_card := hsourceMassCard
    shaded_mass := hsourceMass }

/-- Turn any arbitrarily-small Lemma-31 derivative producer into the
corresponding Lemma-32 derivative-band producer. -/
theorem pureWZ2_lemma32_derivative_band_assembly_of_lemma31_producer
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (epsilon deltaBound : ℝ)
    (lemma31Producer : ∀ requestedBound : ℝ, 0 < requestedBound →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ requestedBound ∧
        Nonempty (PureWZ2Lemma31DerivativeAssembly sigma epsilon delta))
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      Nonempty (PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) := by
  rcases lemma31Producer deltaBound hdeltaBound with
    ⟨delta, hdelta, hdeltaBound', ⟨lemma31⟩⟩
  rcases lemma31.toLemma32DerivativeBand with ⟨band⟩
  exact ⟨delta, hdelta, hdeltaBound', ⟨band⟩⟩

end Kakeya.Assouad
end
