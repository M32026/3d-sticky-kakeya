import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseBalancedFiniteLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandFiniteLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCVPackage

/-!
# Finite Lipschitz output of the balanced high-multiplicity dichotomy

This module keeps the dense and sparse quantitative losses separate.  The
common conclusion is geometric: in either branch there is a genuine cubical
subshading carrying a weak plane map with the requested finite Lipschitz
coefficient.  The branch-specific incidence and mass factors are recorded by
equalities rather than hidden behind a coarse maximum.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def denseBalancedFiniteLeftFactor
    (delta sigma loss : ℝ) (N : ℕ) : ENNReal :=
  (∏ coordinate ∈ Finset.range N,
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 48) *
    (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 48) *
    (1 / 4)

def denseBalancedFiniteRightFactor
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (kappa eta : ℝ) (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (variationScale : ℕ → ℝ) : ENNReal :=
  2 * (denseLocalDirectionLabelCount kappa eta : ENNReal) *
    (∏ coordinate ∈ Finset.range N,
      (localPlaneMapCapCount
        (8 * eta + 16 * (hcwa.chosenNearby (requested coordinate)).rho)
        (variationScale coordinate) : ENNReal) *
        27 * (2 * (denseLocalDirectionLabelCount kappa eta : ENNReal))) *
    27

def sparseBalancedFiniteLeftFactor
    (delta sigma loss : ℝ) (N : ℕ) : ENNReal :=
  (1 / 32 : ENNReal) *
    (∏ coordinate ∈ Finset.range N,
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 24) ^ 2)

def sparseBalancedFiniteRightFactor
    {delta sigma loss kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (variationScale : ℕ → ℝ)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)))
    (package : SparseRelativeBandCVPackage ambient prepared) : ENNReal :=
  (prepared.bandCount : ENNReal) *
    ((∏ coordinate ∈ Finset.range N,
      27 * (2 *
        (wz1OrientationCapCount
          (10 *
              (package.tau / kappa +
                4 * (hcwa.chosenNearby (requested coordinate)).rho) /
            (kappa -
              8 * (hcwa.chosenNearby (requested coordinate)).rho))
          (variationScale coordinate) : ENNReal))) *
      27)

/-- A common dependent output which remembers which quantitative formula was
used.  The sparse witness includes the actual relative band and CV package. -/
structure HighMultiplicityBalancedFiniteLipschitzOutput
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambient : WZ1PaperTubeShading family)
    {nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (variationScale : ℕ → ℝ) where
  incidence : ℝ
  leftFactor : ENNReal
  rightFactor : ENNReal
  refinement : QuantitativeWeakLipschitzPlaneMapRefinement ambient
    incidence (Real.toNNReal coefficient) leftFactor rightFactor
  branch_formula :
    (incidence = eta ∧
      leftFactor = denseBalancedFiniteLeftFactor delta sigma loss N ∧
      rightFactor = denseBalancedFiniteRightFactor
        hcwa kappa eta N requested variationScale) ∨
    ∃ (prepared : SparseRelativeBandPreparationData
        (kappa := kappa) ambient
        (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)))
      (package : SparseRelativeBandCVPackage ambient prepared),
      incidence = package.tau / kappa ∧
      leftFactor = sparseBalancedFiniteLeftFactor delta sigma loss N ∧
      rightFactor = sparseBalancedFiniteRightFactor
        hcwa N requested variationScale prepared package

/-- Consume either side of the balanced high-multiplicity dichotomy.  The
sparse CV package is supplied only for the preparation actually selected by
the sparse branch; no hereditary sticky or arbitrary-subshading CWA premise
is introduced. -/
theorem high_multiplicity_balanced_weak_finite_lipschitz_coefficient
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambient : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant)
    (hfamily : family.Nonempty)
    (hline : WZ1PaperIsLineClass family)
    (dichotomy : HighMultiplicityBalancedDichotomyData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss)),
        Nonempty (SparseRelativeBandCVPackage ambient prepared))
    (N : ℕ)
    (requested : ℕ → WZ2PaperRequestedScale delta)
    (spatialScale variationScale : ℕ → ℝ)
    (K : ℕ → ℕ)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hdelta : 0 < delta)
    (heta : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < N →
      (hcwa.chosenNearby (requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀ coordinate, coordinate < N →
      8 * (hcwa.chosenNearby (requested coordinate)).rho < kappa)
    (hspatialPositive : ∀ coordinate, coordinate < N →
      0 < spatialScale coordinate)
    (hvariationPositive : ∀ coordinate, coordinate < N →
      0 < variationScale coordinate)
    (hK : ∀ coordinate, coordinate < N → 0 < K coordinate)
    (hspatialAligned : ∀ coordinate, coordinate < N →
      spatialScale coordinate = (K coordinate : ℝ) * delta)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
      ∃ coordinate, coordinate < N ∧ d ≤ spatialScale coordinate ∧
        variationScale coordinate ≤ coefficient * d) :
    Nonempty (HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) ambient hcwa N requested variationScale) := by
  cases dichotomy with
  | dense m R high denseCells selected center planeMap R_def R_pos budget
      upper_budget density_lower high_subshading dense_subshading
      selected_subshading selected_cubical center_measurable cluster
      center_cellwise planeMap_cellwise coordination_density mass_retention =>
      rcases dense_balanced_weak_finite_lipschitz_coefficient
          hcwa hfamily hline
          (fun index =>
            (selected_subshading index).trans <|
              (dense_subshading index).trans (high_subshading index))
          selected_cubical center center_measurable center_cellwise cluster
          coordination_density mass_retention N requested spatialScale
          variationScale hkappaNonnegative hkappaHalf hdelta heta hetaHalf
          hcoefficient hactualSmall hspatialPositive hvariationPositive K hK
          hspatialAligned hcovers with
        ⟨refinement⟩
      exact ⟨{
        incidence := eta
        leftFactor := denseBalancedFiniteLeftFactor delta sigma loss N
        rightFactor := denseBalancedFiniteRightFactor
          hcwa kappa eta N requested variationScale
        refinement := refinement
        branch_formula := Or.inl ⟨rfl, rfl, rfl⟩
      }⟩
  | sparse m R high sparseCells R_def R_pos budget upper_budget density_lower
      coordination_density high_subshading sparse_subshading sparse_cubical
      multiplicity_lower close_count mass_retention =>
      have hsparseSub : PaperIsSubshading sparseCells ambient := fun index =>
        (sparse_subshading index).trans (high_subshading index)
      rcases sparse_relative_band_preparation
          (Kakeya.realRpowENN delta (2 - sigma + 3 * loss))
          m R (by omega) R_pos budget upper_budget hsparseSub sparse_cubical
          multiplicity_lower close_count density_lower mass_retention with
        ⟨prepared⟩
      rcases hsparsePackage prepared with ⟨package⟩
      rcases sparse_relative_band_packaged_weak_finite_lipschitz_coefficient
          hcwa hfamily hline prepared package hdelta hkappaPositive
          hcoefficient N requested spatialScale variationScale hactualSmall
          hparentKappa K hK hspatialPositive hvariationPositive
          hspatialAligned hcovers with
        ⟨refinement⟩
      exact ⟨{
        incidence := package.tau / kappa
        leftFactor := sparseBalancedFiniteLeftFactor delta sigma loss N
        rightFactor := sparseBalancedFiniteRightFactor
          hcwa N requested variationScale prepared package
        refinement := refinement
        branch_formula := Or.inr ⟨prepared, package, rfl, rfl, rfl⟩
      }⟩

/-- The selected branch formula always gives a strictly positive factor on
the source mass. -/
lemma HighMultiplicityBalancedFiniteLipschitzOutput.leftFactor_pos
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    {hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant}
    {N : ℕ}
    {requested : ℕ → WZ2PaperRequestedScale delta}
    {variationScale : ℕ → ℝ}
    (finite : HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) source hcwa N requested variationScale)
    (hdelta : 0 < delta) :
    0 < finite.leftFactor := by
  have hpower : 0 < Kakeya.realRpowENN delta
      (2 - sigma + 3 * loss) := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  rcases finite.branch_formula with hdense | hsparse
  · rw [hdense.2.1, denseBalancedFiniteLeftFactor]
    have hquotient : 0 <
        Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 48 :=
      ENNReal.div_pos hpower.ne' (by norm_num)
    have hproduct : 0 <
        ∏ _coordinate ∈ Finset.range N,
          Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 48 := by
      rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro _coordinate _
      exact hquotient.ne'
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hproduct.ne' hquotient.ne').ne' (by norm_num)
  · rcases hsparse with ⟨prepared, package, _hincidence, hleft, _hright⟩
    rw [hleft, sparseBalancedFiniteLeftFactor]
    have hquotient : 0 <
        Kakeya.realRpowENN delta (2 - sigma + 3 * loss) / 24 :=
      ENNReal.div_pos hpower.ne' (by norm_num)
    have hproduct : 0 <
        ∏ _coordinate ∈ Finset.range N,
          (Kakeya.realRpowENN delta
            (2 - sigma + 3 * loss) / 24) ^ 2 := by
      rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro _coordinate _
      exact (ENNReal.pow_pos hquotient 2).ne'
    exact ENNReal.mul_pos (by norm_num) hproduct.ne'

/-- The selected branch formula always gives a finite factor on the source
mass. -/
lemma HighMultiplicityBalancedFiniteLipschitzOutput.leftFactor_ne_top
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    {hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant}
    {N : ℕ}
    {requested : ℕ → WZ2PaperRequestedScale delta}
    {variationScale : ℕ → ℝ}
    (finite : HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) source hcwa N requested variationScale) :
    finite.leftFactor ≠ ⊤ := by
  rcases finite.branch_formula with hdense | hsparse
  · rw [hdense.2.1, denseBalancedFiniteLeftFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.prod_ne_top fun _ _ => ENNReal.div_ne_top
          (by simp [Kakeya.realRpowENN]) (by norm_num))
        (ENNReal.div_ne_top (by simp [Kakeya.realRpowENN]) (by norm_num)))
      (by norm_num)
  · rcases hsparse with ⟨_prepared, _package, _hincidence, hleft, _hright⟩
    rw [hleft, sparseBalancedFiniteLeftFactor]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.prod_ne_top fun _ _ => ENNReal.pow_ne_top
        (ENNReal.div_ne_top (by simp [Kakeya.realRpowENN]) (by norm_num))

/-- The selected branch formula always gives a finite factor on the retained
shading mass. -/
lemma HighMultiplicityBalancedFiniteLipschitzOutput.rightFactor_ne_top
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    {hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant}
    {N : ℕ}
    {requested : ℕ → WZ2PaperRequestedScale delta}
    {variationScale : ℕ → ℝ}
    (finite : HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) source hcwa N requested variationScale) :
    finite.rightFactor ≠ ⊤ := by
  rcases finite.branch_formula with hdense | hsparse
  · rw [hdense.2.2, denseBalancedFiniteRightFactor]
    have hproduct :
        (∏ coordinate ∈ Finset.range N,
          (localPlaneMapCapCount
            (8 * eta + 16 *
              (hcwa.chosenNearby (requested coordinate)).rho)
            (variationScale coordinate) : ENNReal) *
            27 * (2 *
              (denseLocalDirectionLabelCount kappa eta : ENNReal))) ≠
          ⊤ := by
      apply ENNReal.prod_ne_top
      intro coordinate _
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by simp) (by norm_num))
        (ENNReal.mul_ne_top (by norm_num) (by simp))
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (by simp)) hproduct)
      (by norm_num)
  · rcases hsparse with ⟨prepared, package, _hincidence, _hleft, hright⟩
    rw [hright, sparseBalancedFiniteRightFactor]
    have hproduct :
        (∏ coordinate ∈ Finset.range N,
          27 * (2 *
            (wz1OrientationCapCount
              (10 *
                  (package.tau / kappa + 4 *
                    (hcwa.chosenNearby (requested coordinate)).rho) /
                (kappa - 8 *
                  (hcwa.chosenNearby (requested coordinate)).rho))
              (variationScale coordinate) : ENNReal))) ≠ ⊤ := by
      apply ENNReal.prod_ne_top
      intro coordinate _
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) (by simp))
    exact ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top hproduct (by norm_num))

/-- Every quantitative balanced finite-planiness output has positive retained
mass as soon as its source has positive mass.  This is the non-vacuity
certificate needed by the later aligned multiplicity band. -/
lemma HighMultiplicityBalancedFiniteLipschitzOutput.refinement_mass_pos
    {delta sigma loss kappa eta coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {nearbyConstant : ENNReal}
    {hcwa : WZ2PaperPureCWAAtNearbyScales family nearbyConstant}
    {N : ℕ}
    {requested : ℕ → WZ2PaperRequestedScale delta}
    {variationScale : ℕ → ℝ}
    (finite : HighMultiplicityBalancedFiniteLipschitzOutput
      (sigma := sigma) (loss := loss) (kappa := kappa) (eta := eta)
      (coefficient := coefficient) source hcwa N requested variationScale)
    (hdelta : 0 < delta)
    (hsource : 0 < source.mass) :
    0 < finite.refinement.shading.mass := by
  have hleft := finite.leftFactor_pos hdelta
  have hleftSource : 0 < finite.leftFactor * source.mass :=
    ENNReal.mul_pos hleft.ne' hsource.ne'
  by_contra hnot
  have hzero : finite.refinement.shading.mass = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  have hretention := finite.refinement.mass_retention
  rw [hzero, mul_zero] at hretention
  exact (not_le_of_gt hleftSource) hretention

/-- A cropped extremal shading has positive aggregate shaded mass. -/
lemma cropped_extremal_shading_mass_pos
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family shading)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24) :
    0 < shading.mass := by
  have hbodyPos : 0 < (wz1PaperBodyFamily family).mass := by
    have hpowerPos : 0 < Kakeya.realRpowENN delta 2 := by
      exact ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos extremal.delta_pos 2)
    have hcardPos : 0 < family.enncard := by
      change 0 < (family.card : ENNReal)
      exact_mod_cast extremal.nonempty
    have hlower := paperBodyFamily_mass_lower_rpow_two
      extremal.delta_pos (hdeltaSmall.trans (by norm_num)) hline
    exact (ENNReal.mul_pos hpowerPos.ne' hcardPos.ne').trans_le hlower
  have hdensityPos : 0 < Kakeya.realRpowENN delta loss := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos extremal.delta_pos loss)
  exact (ENNReal.mul_pos hdensityPos.ne' hbodyPos.ne').trans_le
    extremal.dense

end Kakeya.Assouad.PureWZ2

end
