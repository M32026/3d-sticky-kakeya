import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicAlignedScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.MassPopularSubband

/-!
# Scale bounds for the Section-6 exact triangular retubing

The selected subband has length `rho / 5000`, so the unrounded target radius
is exactly `80000 * delta / rho`.  Reciprocal-grid alignment enlarges it by
less than two.  These bounds are shared by the final CWA, density, volume,
and AD absorptions.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2MassPopularSubbandData

theorem anisotropic_rawScale_eq
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    anisotropicPaperRawScale delta subband.left subband.right =
      80000 * delta / band.lemma31.data.rho.1 := by
  unfold anisotropicPaperRawScale
  rw [subband.length_eq, band.length_eq]
  have hrho : 0 < band.lemma31.data.rho.1 :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1
  field_simp [hrho.ne']
  ring

theorem anisotropic_rawScale_pos
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    0 < anisotropicPaperRawScale delta subband.left subband.right := by
  unfold anisotropicPaperRawScale
  exact div_pos
    (mul_pos (by norm_num) band.lemma31.data.cfg.extremal.delta_pos)
    (sub_pos.mpr subband.ordered)

theorem anisotropic_rawScale_le_half
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    anisotropicPaperRawScale delta subband.left subband.right ≤ 1 / 2 := by
  let rho := band.lemma31.data.rho.1
  have hrho : 0 < rho :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1
  rw [subband.anisotropic_rawScale_eq, div_le_iff₀ hrho]
  have hfactor : 0 ≤ (1 / 2 : ℝ) - 80000 * rho := by
    dsimp only [rho]
    linarith [band.lemma31.rho_tiny]
  nlinarith [band.lemma31.delta_le_rho_sq,
    mul_nonneg hrho.le hfactor]

theorem anisotropic_alignedScale_pos
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    0 < anisotropicPaperAlignedScale delta subband.left subband.right :=
  anisotropicPaperAlignedScale_pos subband.anisotropic_rawScale_pos
    subband.anisotropic_rawScale_le_half

theorem anisotropic_alignedScale_upper
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    anisotropicPaperAlignedScale delta subband.left subband.right <
      160000 * delta / band.lemma31.data.rho.1 := by
  calc
    anisotropicPaperAlignedScale delta subband.left subband.right <
        2 * anisotropicPaperRawScale delta subband.left subband.right :=
      anisotropicPaperAlignedScale_lt_two_mul_raw
        subband.anisotropic_rawScale_pos
        subband.anisotropic_rawScale_le_half
    _ = 160000 * delta / band.lemma31.data.rho.1 := by
      rw [subband.anisotropic_rawScale_eq]
      ring

theorem delta_le_anisotropic_alignedScale
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    delta ≤ anisotropicPaperAlignedScale delta subband.left subband.right := by
  have hlengthPos : 0 < subband.right - subband.left :=
    sub_pos.mpr subband.ordered
  calc
    delta ≤ 16 * delta / (subband.right - subband.left) := by
      rw [le_div_iff₀ hlengthPos]
      have hlengthSmall : subband.right - subband.left ≤ 16 := by
        rw [subband.length_eq, band.length_eq]
        linarith [band.lemma31.rho_tiny]
      nlinarith [band.lemma31.data.cfg.extremal.delta_pos]
    _ = anisotropicPaperRawScale delta subband.left subband.right := rfl
    _ ≤ anisotropicPaperAlignedScale delta subband.left subband.right :=
      anisotropicPaperRawScale_le_aligned
        subband.anisotropic_rawScale_pos
        subband.anisotropic_rawScale_le_half

theorem anisotropic_alignedScale_le_rho
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    anisotropicPaperAlignedScale delta subband.left subband.right ≤
      160000 * band.lemma31.data.rho.1 := by
  have hrho : 0 < band.lemma31.data.rho.1 :=
    band.lemma31.data.cfg.extremal.delta_pos.trans_le
      band.lemma31.data.rho.2.1
  have hdeltaRho : delta / band.lemma31.data.rho.1 ≤
      band.lemma31.data.rho.1 := by
    rw [div_le_iff₀ hrho]
    simpa [pow_two] using band.lemma31.delta_le_rho_sq
  apply subband.anisotropic_alignedScale_upper.le.trans
  rw [show 160000 * delta / band.lemma31.data.rho.1 =
      160000 * (delta / band.lemma31.data.rho.1) by ring]
  exact mul_le_mul_of_nonneg_left hdeltaRho
    (show (0 : ℝ) ≤ 160000 by norm_num)

theorem anisotropic_alignedScale_le_twenty_four
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    anisotropicPaperAlignedScale delta subband.left subband.right ≤ 1 / 24 := by
  calc
    anisotropicPaperAlignedScale delta subband.left subband.right ≤
        160000 * band.lemma31.data.rho.1 :=
      subband.anisotropic_alignedScale_le_rho
    _ ≤ 1 / 24 := by nlinarith [band.lemma31.rho_tiny]

end PureWZ2MassPopularSubbandData

end Kakeya.Assouad

end
