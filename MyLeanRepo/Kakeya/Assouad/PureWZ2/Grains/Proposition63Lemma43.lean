import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBalancedDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicDirectionDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedDirectionDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicMultiplicityDensity
import MyLeanRepo.Kakeya.Assouad.WZ1.CardinalityBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCVPackage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperBroadMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseWeakPlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseQ1PlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakPlaninessPropertyPHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancing

/-!
# The Lemma 4.3 step in Proposition 6.3

This module isolates exactly the step at lines 235--253 of `wz2_63.tex`.
Starting from the supplied rescaled cropped extremal pair, it keeps the tube
family fixed, refines only the shading, and constructs the new weak plane map
provided by the analogue of [16, Lemma 4.3].  It does not reuse the plane map
from before the unit rescaling, and it does not perform the later Lemma 4.7
Lipschitz regularization.

The two branches below are the usual proof of weak planiness: the dense-close
branch directly chooses a normal to one direction cluster, while the sparse
branch removes the counted broad set and chooses a transverse pair.  Their
different quantitative losses are retained explicitly so that extremality is
restored on the actual selected shading.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The one-sided loss associated to a two-sided mass inequality
`left * source.mass <= right * selected.mass`. -/
def proposition63Lemma43MassLoss (left right : ENNReal) : ENNReal :=
  1 + left⁻¹ * right

lemma proposition63Lemma43MassLoss_pos (left right : ENNReal) :
    0 < proposition63Lemma43MassLoss left right := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

lemma proposition63Lemma43MassLoss_ne_top
    {left right : ENNReal}
    (hleft : 0 < left) (hright : right ≠ ⊤) :
    proposition63Lemma43MassLoss left right ≠ ⊤ := by
  rw [proposition63Lemma43MassLoss, ENNReal.add_ne_top]
  exact ⟨by norm_num, ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr hleft.ne') hright⟩

lemma proposition63Lemma43MassLoss_inv_mul_le
    {left right sourceMass selectedMass : ENNReal}
    (hleft : 0 < left) (hleftTop : left ≠ ⊤)
    (hrightTop : right ≠ ⊤)
    (hmass : left * sourceMass ≤ right * selectedMass) :
    (proposition63Lemma43MassLoss left right)⁻¹ * sourceMass ≤
      selectedMass := by
  have hmassLossPos : 0 < proposition63Lemma43MassLoss left right :=
    proposition63Lemma43MassLoss_pos left right
  have hmassLossTop : proposition63Lemma43MassLoss left right ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top hleft hrightTop
  apply (ENNReal.inv_mul_le_iff hmassLossPos.ne' hmassLossTop).2
  calc
    sourceMass = left⁻¹ * (left * sourceMass) := by
      rw [ENNReal.inv_mul_cancel_left hleft.ne' hleftTop]
    _ ≤ left⁻¹ * (right * selectedMass) := by
      exact mul_le_mul_left' hmass _
    _ = (left⁻¹ * right) * selectedMass := by ring
    _ ≤ proposition63Lemma43MassLoss left right * selectedMass := by
      gcongr
      exact le_add_left le_rfl

/-- The paper-faithful pointwise weak-plane-map refinement core.

The family is definitionally unchanged and the map is only required to satisfy
the pointwise incidence bound.  In particular, this record contains no
cellwise constancy: that property is created at the coarse scale by the
Lemma 4.4 analogue. -/
structure Proposition63PointwiseWeakMapRefinementData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (incidenceBudget : ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  planeMap : PaperWZ1WeakPlaneMapData shading incidenceBudget
  leftFactor : ENNReal
  rightFactor : ENNReal
  leftFactor_pos : 0 < leftFactor
  leftFactor_ne_top : leftFactor ≠ ⊤
  rightFactor_ne_top : rightFactor ≠ ⊤
  mass_retention : leftFactor * source.mass ≤ rightFactor * shading.mass

/-- The Proposition 6.3 wrapper around the pointwise Lemma 4.3 refinement.
Cubicality is the formal invariant needed by later selections, and extremality
is restored from the mass receipt before the next paper step.  Cellwise
constancy is deliberately absent: the Lemma 4.4 analogue creates it by
sampling the fine map on coarse cells. -/
structure Proposition63Lemma43Data
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (incidenceBudget : ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading source
  planeMap : PaperWZ1WeakPlaneMapData shading incidenceBudget
  leftFactor : ENNReal
  rightFactor : ENNReal
  leftFactor_pos : 0 < leftFactor
  leftFactor_ne_top : leftFactor ≠ ⊤
  rightFactor_ne_top : rightFactor ≠ ⊤
  mass_retention : leftFactor * source.mass ≤ rightFactor * shading.mass
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal
    sigma targetLoss family shading

namespace Proposition63Lemma43Data

/-- Forget the Proposition 6.3 wrapper fields, retaining the paper-faithful
pointwise refinement on the same family and shading. -/
def toPointwise
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {incidenceBudget : ℝ}
    (data : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) :
    Proposition63PointwiseWeakMapRefinementData
      source incidenceBudget where
  shading := data.shading
  subshading := data.subshading
  planeMap := data.planeMap
  leftFactor := data.leftFactor
  rightFactor := data.rightFactor
  leftFactor_pos := data.leftFactor_pos
  leftFactor_ne_top := data.leftFactor_ne_top
  rightFactor_ne_top := data.rightFactor_ne_top
  mass_retention := data.mass_retention

def massLoss
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {incidenceBudget : ℝ}
    (data : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) : ENNReal :=
  proposition63Lemma43MassLoss data.leftFactor data.rightFactor

lemma massLoss_pos
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {incidenceBudget : ℝ}
    (data : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) :
    0 < data.massLoss :=
  proposition63Lemma43MassLoss_pos _ _

lemma massLoss_ne_top
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {incidenceBudget : ℝ}
    (data : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) :
    data.massLoss ≠ ⊤ :=
  proposition63Lemma43MassLoss_ne_top
    data.leftFactor_pos data.rightFactor_ne_top

lemma massLoss_inv_mul_source_mass_le
    {delta sigma sourceLoss targetLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {incidenceBudget : ℝ}
    (data : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) :
    data.massLoss⁻¹ * source.mass ≤ data.shading.mass :=
  proposition63Lemma43MassLoss_inv_mul_le
    data.leftFactor_pos data.leftFactor_ne_top
    data.rightFactor_ne_top data.mass_retention

end Proposition63Lemma43Data

/-- Enlarge the incidence budget without changing the weak plane map. -/
def paperWeakPlaneMapMono
    {delta firstBudget secondBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hbudget : firstBudget ≤ secondBudget)
    (data : PaperWZ1WeakPlaneMapData shading firstBudget) :
    PaperWZ1WeakPlaneMapData shading secondBudget where
  planeMap := data.planeMap
  measurable := data.measurable
  unit := data.unit
  incidence index point hpoint :=
    (data.incidence index point hpoint).trans hbudget

/-- The dense-branch mass factors in the Proposition 6.3 Lemma 4.3 step. -/
def proposition63Lemma43DenseLeftFactor
    (delta sigma sourceLoss : ℝ) : ENNReal :=
  (Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss) / 48) *
    (1 / 4)

def proposition63Lemma43DenseMassLoss
    (delta sigma sourceLoss : ℝ) : ENNReal :=
  proposition63Lemma43MassLoss
    (proposition63Lemma43DenseLeftFactor delta sigma sourceLoss) 2

/-- The sparse-branch loss after the relative multiplicity band, broad-set
deletion, and transverse-pair selection. -/
def proposition63Lemma43SparseMassLoss
    {delta sigma sourceLoss kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) source
      (Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss))) : ENNReal :=
  proposition63Lemma43MassLoss (1 / 32) prepared.bandCount

/-- The mass loss in the literal Lemma 11 route: one half for the initial
high-multiplicity restriction, one dyadic multiplicity band, one half for
deleting the broad set, and one quarter for selecting the good third
directions. -/
def proposition63PaperLemma43MassLoss
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (high : WZ1PaperTubeShading family)
    (band : WZ2PaperGlobalMultiplicityBandData high) : ENNReal :=
  proposition63Lemma43MassLoss (1 / 16)
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)

/-- The common loss used by the paper-order dyadic Lemma 4.3 argument.

After one dyadic multiplicity band, the balanced dense branch loses at most
`96`, while the sparse branch loses at most `16` after broad pruning and
third-direction selection.  The common factor below therefore covers both
branches. -/
def proposition63DyadicLemma43MassLoss
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) : ENNReal :=
  proposition63Lemma43MassLoss 1
    (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) * 96)

/-- Proposition 6.3's Lemma 4.3 step with only a dyadic logarithmic loss.

This is the branch structure used in the paper proof.  A dyadic multiplicity
band is selected first.  Dense cells already carry a cellwise weak plane map.
On sparse cells the counted broad set is removed with `Q = m^3/4`, after
which a cellwise transverse-pair normal gives the weak plane map.  The lower
bound on `m` is derived from extremality and the retained dyadic mass, rather
than imposed through a power-sized preliminary restriction. -/
theorem proposition63_dyadic_lemma43_weak_plane_map
    {delta sigma sourceLoss targetLoss densityLoss tauExponent kappa tau
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hbandDensityAbsorb :
      (2 * (((Nat.log 2 family.card + 1 : ℕ) : ENNReal))) *
          Kakeya.realRpowENN delta sourceLoss ≤ 1)
    (hfixedAbsorb :
      (144 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * sourceLoss))
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hcardinality : (family.card : ℝ) ≤
      (99 : ℝ) ^ 6 * Real.rpow delta (-6 - sourceLoss))
    (hlogAbsorb :
      2 * (Real.log
          ((99 : ℝ) ^ 6 * Real.rpow delta (-6 - sourceLoss)) /
            Real.log 2 + 1) ≤
        Real.rpow delta ((sourceLoss - targetLoss) / 2))
    (hlemma43FixedAbsorb :
      (49 : ENNReal) ≤
        Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2))
    (hsourceLoss : 0 < sourceLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hkappa : 0 < kappa)
    (htau : 0 < tau)
    (htauPower : ENNReal.ofReal tau =
      Kakeya.realRpowENN delta tauExponent)
    (hdenseIncidence : kappa ≤ incidenceBudget)
    (hsparseIncidence : tau / kappa ≤ incidenceBudget)
    (hpowerSmall :
      (8192 : ENNReal) *
          (((Nat.log 2 family.card + 1 : ℕ) : ENNReal)) ^ 2 * C ^ 2 ≤
        Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * sourceLoss)) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  let logCount : ENNReal :=
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
  let rightFactor : ENNReal := logCount * 96
  have hrightTop : rightFactor ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · norm_num
  have _hlogPower :
      (2 : ENNReal) * logCount ≤
        Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2) := by
    have hraw := cardinality_bound_from_poly sourceExtremal.delta_pos
      (C := (99 : ℝ) ^ 6) (N := 6 + sourceLoss)
      (eta := (sourceLoss - targetLoss) / 2)
      (epsilon_ref := 0)
      sourceExtremal.delta_le_one sourceExtremal.nonempty
      (by norm_num) (by linarith : 0 ≤ (6 + sourceLoss))
      (by simpa [show -6 - sourceLoss = -(6 + sourceLoss) by ring]
        using hcardinality)
      (by
        convert hlogAbsorb using 1 <;> ring)
    dsimp only [logCount]
    simpa only [Nat.cast_add, Nat.cast_one, sub_zero] using hraw
  have hlogCountOne : (1 : ENNReal) ≤ logCount := by
    dsimp only [logCount]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      Nat.log 2 family.card + 1 ≠ 0)
  have hlossBound : proposition63DyadicLemma43MassLoss family ≤
      (49 : ENNReal) * ((2 : ENNReal) * logCount) := by
    rw [proposition63DyadicLemma43MassLoss,
      proposition63Lemma43MassLoss]
    simp only [inv_one, one_mul]
    calc
      1 + (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) * 96) =
          1 + logCount * 96 := by rfl
      _ ≤ logCount + logCount * 96 := by gcongr
      _ = (97 : ENNReal) * logCount := by ring
      _ ≤ (98 : ENNReal) * logCount := by gcongr; norm_num
      _ = (49 : ENNReal) * (2 * logCount) := by ring
  have hgapSplit :
      Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2) *
          Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2) =
        Kakeya.realRpowENN delta (sourceLoss - targetLoss) := by
    rw [← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos]
    congr 1
    ring
  have hlossPower : proposition63DyadicLemma43MassLoss family ≤
      Kakeya.realRpowENN delta (sourceLoss - targetLoss) := by
    calc
      proposition63DyadicLemma43MassLoss family ≤
          (49 : ENNReal) * ((2 : ENNReal) * logCount) := hlossBound
      _ ≤ Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2) *
          Kakeya.realRpowENN delta ((sourceLoss - targetLoss) / 2) := by
        exact mul_le_mul hlemma43FixedAbsorb _hlogPower bot_le bot_le
      _ = Kakeya.realRpowENN delta (sourceLoss - targetLoss) := hgapSplit
  have hrestore : proposition63DyadicLemma43MassLoss family *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss := by
    calc
      proposition63DyadicLemma43MassLoss family *
            Kakeya.realRpowENN delta targetLoss ≤
          Kakeya.realRpowENN delta (sourceLoss - targetLoss) *
            Kakeya.realRpowENN delta targetLoss := by gcongr
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← Kakeya.Assouad.realRpowENN_add sourceExtremal.delta_pos]
        congr 1
        ring
  rcases wz2_paper_global_multiplicity_band source sourceExtremal.cubical with
    ⟨band⟩
  let m : ℕ := 2 ^ band.level
  have hbandSub : PaperIsSubshading band.band source := by
    intro index point hpoint
    rw [band.band_eq] at hpoint
    exact hpoint.1
  have hbandMass : source.mass ≤ logCount * band.band.mass := by
    have hdivision := band.band_mass_retention
    have hlogPos : 0 < logCount := by
      dsimp only [logCount]
      exact_mod_cast Nat.zero_lt_succ (Nat.log 2 family.card)
    have hlogTop : logCount ≠ ⊤ := by
      exact ENNReal.natCast_ne_top _
    change source.mass / logCount ≤ band.band.mass at hdivision
    rw [ENNReal.div_le_iff hlogPos.ne' hlogTop] at hdivision
    simpa [mul_comm] using hdivision
  have hbandLower : ∀ point ∈ band.band.union,
      m ≤ band.band.pointMultiplicity point := by
    intro point hpoint
    exact_mod_cast (band.band_multiplicity point hpoint).1
  have hbandUpper : ∀ point ∈ band.band.union,
      band.band.pointMultiplicity point < 2 * m := by
    intro point hpoint
    have hupper :
        (band.band.pointMultiplicity point : ENNReal) <
          ((2 * m : ℕ) : ENNReal) := by
      simpa [m, pow_succ, mul_comm] using
        (band.band_multiplicity point hpoint).2
    exact_mod_cast hupper
  have hdensity : Kakeya.realRpowENN delta densityLoss *
      family.enncard ≤ (m : ENNReal) :=
    dyadic_branch_multiplicity_density sourceExtremal hline
      (hdeltaSmall.trans (by norm_num))
      hbandSub hbandMass hbandUpper hdensityLoss (by
        simpa [logCount] using hbandDensityAbsorb)
  have hmTwelve : 12 ≤ m :=
    twelve_le_multiplicity_of_density_power sourceExtremal hdeltaSmall
      hdensityLoss hfixedAbsorb hdensity
  rcases balanced_direction_dichotomy sourceExtremal.nonempty
      band.band_cubical m hmTwelve hbandLower hbandUpper with ⟨dichotomy⟩
  cases dichotomy with
  | dense R denseCells selected center planeMap R_def R_pos budget
      denseSub selectedSub selectedCubical centerMeasurable cluster
      centerCell planeCell multiplicityLower massRetention =>
      have hselectedSource : PaperIsSubshading selected source :=
        fun index => (selectedSub index).trans <|
          (denseSub index).trans (hbandSub index)
      have hmass : (1 : ENNReal) * source.mass ≤
          rightFactor * selected.mass := by
        rw [one_mul]
        calc
          source.mass ≤ logCount * band.band.mass := hbandMass
          _ ≤ logCount * (96 * selected.mass) := by gcongr
          _ = rightFactor * selected.mass := by
            simp only [rightFactor]
            ring
      let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
        paperWeakPlaneMapMono hdenseIncidence planeMap
      have hinverse :
          (proposition63Lemma43MassLoss 1 rightFactor)⁻¹ *
              source.mass ≤ selected.mass :=
        proposition63Lemma43MassLoss_inv_mul_le
          (by norm_num) (by norm_num) hrightTop hmass
      have hextremal : WZ2PaperCroppedIsExtremal
          sigma targetLoss family selected := by
        apply transfer_cropped_extremal_to_subshading
          (proposition63Lemma43MassLoss 1 rightFactor)
          (proposition63Lemma43MassLoss_pos _ _)
          (proposition63Lemma43MassLoss_ne_top (by norm_num) hrightTop)
          sourceExtremal hselectedSource hinverse selectedCubical
          hsourceTarget
        · simpa [proposition63DyadicLemma43MassLoss, rightFactor,
            logCount] using hrestore
        · exact sourceExtremal.delta_pos
        · exact sourceExtremal.delta_le_one
        · exact htargetLoss
      exact ⟨{
        shading := selected
        subshading := hselectedSource
        cubical := selectedCubical
        planeMap := finalMap
        leftFactor := 1
        rightFactor := rightFactor
        leftFactor_pos := by norm_num
        leftFactor_ne_top := by norm_num
        rightFactor_ne_top := hrightTop
        mass_retention := hmass
        extremal := hextremal
      }⟩
  | sparse R sparse R_def R_pos budget sparseSub sparseCubical
      multiplicityLower multiplicityUpper closeCount massRetention =>
      have hsparseSource : PaperIsSubshading sparse source :=
        fun index => (sparseSub index).trans (hbandSub index)
      have hCVSparse : ∀ (E : Set Point3), MeasurableSet E →
          E ⊆ sparse.union → ∀ (L : ENNReal),
            (∀ point ∈ E, L ≤
              (paperShadingTrilinearMultiplicity sparse point) ^
                (1 / 2 : ℝ)) →
            L * volume E ≤
              C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
                (3 / 2 : ℝ) :=
        transfer_cv_to_subshading hsparseSource C hCV
      have hmultiplicityUpper : ∀ point ∈ sparse.union,
          (sparse.pointMultiplicity point : ENNReal) ≤
            (2 * m : ℕ) := by
        intro point hpoint
        exact_mod_cast (multiplicityUpper point hpoint).le
      let Q : ℕ := m ^ 3 / 4
      have hQPos : 0 < Q := by
        dsimp only [Q]
        have hcube : 4 ≤ m ^ 3 := by
          calc
            4 ≤ 2 ^ 3 := by norm_num
            _ ≤ m ^ 3 := Nat.pow_le_pow_left (by omega) 3
        exact Nat.div_pos hcube (by norm_num)
      have hQBudget : 4 * Q ≤ m ^ 3 := by
        dsimp only [Q]
        exact Nat.mul_div_le (m ^ 3) 4
      have hQSixteenth : (1 / 16 : ENNReal) * (m : ENNReal) ^ 3 ≤
          (Q : ENNReal) := by
        have hnat : m ^ 3 ≤ 16 * Q := by
          have hdivision : m ^ 3 = 4 * Q + m ^ 3 % 4 := by
            dsimp only [Q]
            exact (Nat.div_add_mod (m ^ 3) 4).symm
          have hremainder : m ^ 3 % 4 < 4 := Nat.mod_lt _ (by norm_num)
          have hqOne : 1 ≤ Q := hQPos
          omega
        rw [show (1 / 16 : ENNReal) * (m : ENNReal) ^ 3 =
          (m : ENNReal) ^ 3 / 16 by simp [div_eq_mul_inv, mul_comm]]
        apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
        simpa [mul_comm] using (show
          (m ^ 3 : ENNReal) ≤ (16 * Q : ℕ) by exact_mod_cast hnat)
      have hambient :
          Kakeya.realRpowENN delta (sourceLoss + 2) *
              family.enncard ≤ source.mass := by
        have hbody := paperBodyFamily_mass_lower_rpow_two
          sourceExtremal.delta_pos (hdeltaSmall.trans (by norm_num)) hline
        calc
          Kakeya.realRpowENN delta (sourceLoss + 2) *
                family.enncard =
              Kakeya.realRpowENN delta sourceLoss *
                (Kakeya.realRpowENN delta 2 * family.enncard) := by
            rw [Kakeya.Assouad.realRpowENN_add
              sourceExtremal.delta_pos]
            ring
          _ ≤ Kakeya.realRpowENN delta sourceLoss *
              (wz1PaperBodyFamily family).mass := by gcongr
          _ ≤ source.mass := sourceExtremal.dense
      have hquarterSource : (1 / 4 : ENNReal) * source.mass ≤
          logCount * sparse.mass := by
        calc
          (1 / 4 : ENNReal) * source.mass ≤
              (1 / 4 : ENNReal) * (logCount * band.band.mass) := by
            gcongr
          _ ≤ (1 / 4 : ENNReal) *
              (logCount * (2 * sparse.mass)) := by
            gcongr
          _ = (1 / 2 : ENNReal) *
              (logCount * sparse.mass) := by
            calc
              (1 / 4 : ENNReal) * (logCount * (2 * sparse.mass)) =
                  ((1 / 4 : ENNReal) * 2) *
                    (logCount * sparse.mass) := by ring
              _ = (1 / 2 : ENNReal) *
                    (logCount * sparse.mass) := by
                congr 1
                apply (ENNReal.toReal_eq_toReal_iff'
                  (ENNReal.mul_ne_top (by norm_num) (by norm_num))
                  (by norm_num)).mp
                norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
          _ ≤ logCount * sparse.mass := by
            exact mul_le_of_le_one_left bot_le (by norm_num)
      have hmonomial :
          (8192 : ENNReal) * logCount ^ 2 * C ^ 2 *
              (ENNReal.ofReal (delta ^ 2) * family.enncard) ^ 3 ≤
            Kakeya.realRpowENN delta densityLoss *
              ENNReal.ofReal tau *
              Kakeya.realRpowENN delta (sourceLoss + 2) ^ 2 *
              family.enncard ^ 3 := by
        have hraw := sparse_relative_band_power_monomial_budget
          (delta := delta) (sigma := sigma) (loss := sourceLoss)
          (tauExponent := tauExponent) (bandCount := logCount)
          (coefficient := C) (familyCard := family.enncard)
          sourceExtremal.delta_pos (by
            simpa [logCount] using hpowerSmall)
        rw [← htauPower] at hraw
        simpa [hdensityLoss] using hraw
      have hbroadAbsorb :
          (4 : ENNReal) * (m : ENNReal) * C *
              (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
                (3 / 2 : ℝ) ≤
            ((Q : ENNReal) * ENNReal.ofReal tau) ^
                (1 / 2 : ℝ) * sparse.mass := by
        apply sparse_relative_band_absorption_of_monomial_budget
          (bandCount := logCount)
          (densityPower := Kakeya.realRpowENN delta densityLoss)
          (ambientPower := Kakeya.realRpowENN delta (sourceLoss + 2))
        · dsimp only [logCount]
          exact_mod_cast (Nat.zero_lt_succ (Nat.log 2 family.card)).ne'
        · exact ENNReal.natCast_ne_top _
        · calc
            Kakeya.realRpowENN delta densityLoss * family.enncard ≤
                (m : ENNReal) := hdensity
            _ = 1 * (m : ENNReal) := by simp
            _ ≤ 2 * (m : ENNReal) :=
              mul_le_mul_right' (by norm_num) _
        · exact hQSixteenth
        · exact hambient
        · exact hquarterSource
        · exact hmonomial
      have hbroadSmall :
          2 * (∫⁻ point in paperCountedBroadSet sparse tau Q,
            (sparse.pointMultiplicity point : ENNReal)) ≤ sparse.mass :=
        paper_broad_mass_budget_main C hCVSparse (2 * m : ℕ)
          hmultiplicityUpper Q tau hQPos htau (by
            convert hbroadAbsorb using 1
            norm_cast
            ring)
      have hbroadMeasurable :
          MeasurableSet (paperCountedBroadSet sparse tau Q) :=
        paperCountedBroadSet_measurable sparse tau Q
      rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with
        ⟨narrow⟩
      have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
          point ∈ narrow.shading.carrier index →
            paperCloseDirectionCount narrow.shading point index kappa < R := by
        intro point hpoint index hindex
        have hpointSparse : point ∈ sparse.union :=
          ⟨index, narrow.subshading index hindex⟩
        exact (close_count_subshading narrow.subshading).trans_lt
          (closeCount point hpointSparse index
            (narrow.subshading index hindex))
      have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
          narrow.shading.pointMultiplicity point =
            sparse.pointMultiplicity point :=
        fun point hpoint => paper_narrow_pointMultiplicity_eq narrow hpoint
      have hnarrowBudget : ∀ point ∈ narrow.shading.union,
          let mu := narrow.shading.pointMultiplicity point
          4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
        intro point hpoint
        have hmPoint : m ≤ narrow.shading.pointMultiplicity point := by
          rw [hnarrowMultiplicity point hpoint]
          have hpointSparse : point ∈ sparse.union := by
            rcases hpoint with ⟨index, hindex⟩
            exact ⟨index, narrow.subshading index hindex⟩
          exact multiplicityLower point hpointSparse
        exact wz1_good_triple_budget m Q R
          (narrow.shading.pointMultiplicity point) hmPoint hQBudget budget
      rcases paper_cellwise_weak_planiness_from_narrow
          sourceExtremal.delta_pos hkappa sourceExtremal.nonempty
          sparseCubical narrow hnarrowClose hnarrowBudget with
        ⟨selected, selection, planeMap, selectedSub, selectedCubical,
          planeCellwise, selectionCellwise, planeSelection,
          selectedMultiplicity, selectedMass⟩
      have hselectedSource : PaperIsSubshading selected source :=
        fun index => (selectedSub index).trans <|
          (narrow.subshading index).trans (hsparseSource index)
      have hsparseNarrow : sparse.mass ≤ 2 * narrow.shading.mass := by
        have hcancel : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          rw [one_div]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        calc
          sparse.mass = 2 * ((1 / 2 : ENNReal) * sparse.mass) := by
            rw [← mul_assoc, hcancel, one_mul]
          _ ≤ 2 * narrow.shading.mass :=
            mul_le_mul_left' narrow.mass_lower 2
      have hnarrowSelected : narrow.shading.mass ≤ 4 * selected.mass := by
        have hscaled := mul_le_mul_left' selectedMass (4 : ENNReal)
        have hcancel : (4 : ENNReal) * (1 / 4 : ENNReal) = 1 := by
          rw [one_div]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        calc
          narrow.shading.mass =
              4 * ((1 / 4 : ENNReal) * narrow.shading.mass) := by
            rw [← mul_assoc, hcancel, one_mul]
          _ ≤ 4 * selected.mass := hscaled
      have hmass : (1 : ENNReal) * source.mass ≤
          rightFactor * selected.mass := by
        rw [one_mul]
        calc
          source.mass ≤ logCount * band.band.mass := hbandMass
          _ ≤ logCount * (2 * sparse.mass) := by gcongr
          _ ≤ logCount * 2 * (2 * narrow.shading.mass) := by
            simpa [mul_assoc] using
              (mul_le_mul_left' hsparseNarrow (logCount * 2))
          _ = logCount * 4 * narrow.shading.mass := by ring
          _ ≤ logCount * 4 * (4 * selected.mass) := by
            gcongr
          _ = logCount * 16 * selected.mass := by ring
          _ ≤ logCount * 96 * selected.mass := by
            gcongr
            norm_num
          _ = rightFactor * selected.mass := by
            simp only [rightFactor]
      let finalMap :
          PaperWZ1WeakPlaneMapData selected incidenceBudget :=
        paperWeakPlaneMapMono hsparseIncidence planeMap
      have hinverse :
          (proposition63Lemma43MassLoss 1 rightFactor)⁻¹ *
              source.mass ≤ selected.mass :=
        proposition63Lemma43MassLoss_inv_mul_le
          (by norm_num) (by norm_num) hrightTop hmass
      have hextremal : WZ2PaperCroppedIsExtremal
          sigma targetLoss family selected := by
        apply transfer_cropped_extremal_to_subshading
          (proposition63Lemma43MassLoss 1 rightFactor)
          (proposition63Lemma43MassLoss_pos _ _)
          (proposition63Lemma43MassLoss_ne_top (by norm_num) hrightTop)
          sourceExtremal hselectedSource hinverse selectedCubical
          hsourceTarget
        · simpa [proposition63DyadicLemma43MassLoss, rightFactor,
            logCount] using hrestore
        · exact sourceExtremal.delta_pos
        · exact sourceExtremal.delta_le_one
        · exact htargetLoss
      exact ⟨{
        shading := selected
        subshading := hselectedSource
        cubical := selectedCubical
        planeMap := finalMap
        leftFactor := 1
        rightFactor := rightFactor
        leftFactor_pos := by norm_num
        leftFactor_ne_top := by norm_num
        rightFactor_ne_top := hrightTop
        mass_retention := hmass
        extremal := hextremal
      }⟩

private lemma proposition63_nat_lt_ceil_add_one_of_cast_le
    {n : ℕ} {X : ENNReal} (hXTop : X ≠ ⊤)
    (hn : (n : ENNReal) ≤ X) :
    n < Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact (ENNReal.toReal_le_toReal (by simp) hXTop).mpr hn
  exact Nat.lt_succ_of_le <|
    Nat.cast_le.mp (hreal.trans (Nat.le_ceil X.toReal))

/-- The paper-order implementation of the analogue of [16, Lemma 4.3].

Unlike the more general dense/sparse finite-planiness wrapper below, this
theorem follows Lemma 11 verbatim: it first makes a high-multiplicity
whole-cell refinement, then a factor-two multiplicity band, removes the
counted broad set using the multilinear estimate, and finally chooses a
transverse pair whose normalized cross product is the weak plane map. -/
theorem proposition63_paper_lemma43_weak_plane_map
    {delta sigma sourceLoss targetLoss densityLoss kappa tau
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hsourceCWA : WZ2PaperConvexWolffBound family C)
    (hCTop : C ≠ ⊤)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hdeltaSmall : delta ≤ 1 / 10000)
    (hsmall : Kakeya.realRpowENN delta sourceLoss < 1 / 4)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hdeltaKappa : delta ≤ kappa)
    (htau : 0 < tau)
    (hincidence : tau / kappa ≤ incidenceBudget)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * sourceLoss))
    (hcloseBudget : ∀
      (high : WZ1PaperTubeShading family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        let X := C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard
        let R := Nat.ceil X.toReal + 1
        12 * R ≤ 2 ^ band.level)
    (hbroadAbsorb : ∀
      (high : WZ1PaperTubeShading family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        let m := 2 ^ band.level
        let Q : ℕ := m ^ 3 / 4
        (2 : ENNReal) * (2 * m : ℕ) * C *
            (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
              (3 / 2 : ℝ) ≤
          (((Q : ENNReal) * ENNReal.ofReal tau) ^
            (1 / 2 : ℝ)) * band.band.mass)
    (hrestore : ∀
      (high : WZ1PaperTubeShading family)
      (band : WZ2PaperGlobalMultiplicityBandData high),
        proposition63PaperLemma43MassLoss (source := source) high band *
            Kakeya.realRpowENN delta targetLoss ≤
          Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  subst densityLoss
  rcases high_multiplicity_direction_input sourceExtremal hline
      (hdeltaSmall.trans (by norm_num)) rfl hsourceLoss hsmall with
    ⟨m0, high, hhighSub, hhighCubical, hhighMultiplicity, _hdensity,
      hhighMass, _hhighCommon, _hm0Pos⟩
  rcases wz2_paper_global_multiplicity_band high hhighCubical with
    ⟨band⟩
  let m : ℕ := 2 ^ band.level
  let X : ENNReal :=
    C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard
  let R : ℕ := Nat.ceil X.toReal + 1
  let Q : ℕ := m ^ 3 / 4
  have hXTop : X ≠ ⊤ := by
    dsimp only [X]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCTop ENNReal.ofReal_ne_top)
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hRPos : 0 < R := by
    dsimp only [R]
    omega
  have hRBudget : 12 * R ≤ m := by
    simpa [X, R, m] using hcloseBudget high band
  have hmTwelve : 12 ≤ m := by omega
  have hQPos : 0 < Q := by
    dsimp only [Q]
    have : 4 ≤ m ^ 3 := by
      calc
        4 ≤ 2 ^ 3 := by norm_num
        _ ≤ m ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact Nat.div_pos this (by norm_num)
  have hQBudget : 4 * Q ≤ m ^ 3 := by
    dsimp only [Q]
    exact Nat.mul_div_le (m ^ 3) 4
  have hbandLower : ∀ point ∈ band.band.union,
      m ≤ band.band.pointMultiplicity point := by
    intro point hpoint
    exact_mod_cast (band.band_multiplicity point hpoint).1
  have hbandUpper : ∀ point ∈ band.band.union,
      (band.band.pointMultiplicity point : ENNReal) ≤ (2 * m : ℕ) := by
    intro point hpoint
    have hupper := (band.band_multiplicity point hpoint).2.le
    simpa [m, pow_succ, mul_comm] using hupper
  have hbandSubSource : PaperIsSubshading band.band source := fun index =>
    (by
      intro point hpoint
      rw [band.band_eq] at hpoint
      exact hhighSub index hpoint.1)
  have hCVBand : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ band.band.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity band.band point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) :=
    transfer_cv_to_subshading hbandSubSource C hCV
  have hbroadSmall :
      2 * (∫⁻ point in paperCountedBroadSet band.band tau Q,
        (band.band.pointMultiplicity point : ENNReal)) ≤ band.band.mass :=
    paper_broad_mass_budget_main C hCVBand (2 * m : ℕ) hbandUpper
      Q tau hQPos htau (by simpa [m, Q] using hbroadAbsorb high band)
  have hbroadMeasurable :
      MeasurableSet (paperCountedBroadSet band.band tau Q) :=
    paperCountedBroadSet_measurable band.band tau Q
  rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with ⟨narrow⟩
  have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
      point ∈ narrow.shading.carrier index →
        paperCloseDirectionCount narrow.shading point index kappa < R := by
    intro point hpoint index hindex
    have hpointBand : point ∈ band.band.union :=
      ⟨index, narrow.subshading index hindex⟩
    have hcountBand := paper_cwa_close_direction_count
      (coarseShading := band.band) hsourceCWA
      sourceExtremal.delta_pos hdeltaSmall kappa hkappa hkappaOne
      hdeltaKappa point index (narrow.subshading index hindex)
    have hcountNarrow :
        paperCloseDirectionCount narrow.shading point index kappa ≤
          paperCloseDirectionCount band.band point index kappa := by
      unfold paperCloseDirectionCount
      apply Finset.card_le_card
      intro other hother
      simp only [Finset.mem_filter] at hother ⊢
      exact ⟨hother.1, narrow.subshading other hother.2.1, hother.2.2⟩
    have hcountX :
        (paperCloseDirectionCount narrow.shading point index kappa :
          ENNReal) ≤ X := by
      have hcountCast :
          (paperCloseDirectionCount narrow.shading point index kappa :
            ENNReal) ≤
          paperCloseDirectionCount band.band point index kappa := by
        exact_mod_cast hcountNarrow
      exact hcountCast.trans (by simpa [X] using hcountBand)
    exact proposition63_nat_lt_ceil_add_one_of_cast_le hXTop hcountX
  have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity point =
        band.band.pointMultiplicity point :=
    fun point hpoint => paper_narrow_pointMultiplicity_eq narrow hpoint
  have hnarrowBudget : ∀ point ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity point
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro point hpoint
    have hmPoint : m ≤ narrow.shading.pointMultiplicity point := by
      rw [hnarrowMultiplicity point hpoint]
      have hpointBand : point ∈ band.band.union :=
        by
          rcases hpoint with ⟨index, hindex⟩
          exact ⟨index, narrow.subshading index hindex⟩
      exact hbandLower point hpointBand
    exact wz1_good_triple_budget m Q R
      (narrow.shading.pointMultiplicity point) hmPoint hQBudget hRBudget
  rcases paper_cellwise_weak_planiness_from_narrow
      sourceExtremal.delta_pos hkappa sourceExtremal.nonempty
      band.band_cubical narrow hnarrowClose hnarrowBudget with
      ⟨selected, _selection, weakMap, hselectedSub, hselectedCubical,
          hplaneCell, _hselectionCell, _hplaneSelection,
      _hmultiplicity, hselectedMass⟩
  have hselectedSource : PaperIsSubshading selected source := fun index =>
    (hselectedSub index).trans <|
      (narrow.subshading index).trans (hbandSubSource index)
  let bandCount : ENNReal :=
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
  have hbandCountPos : 0 < bandCount := by
    dsimp only [bandCount]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 family.card)
  have hbandCountTop : bandCount ≠ ⊤ := by simp [bandCount]
  have hhighBand : high.mass ≤ bandCount * band.band.mass := by
    have hdivision := band.band_mass_retention
    change high.mass / bandCount ≤ band.band.mass at hdivision
    rw [ENNReal.div_le_iff hbandCountPos.ne' hbandCountTop] at hdivision
    simpa [mul_comm] using hdivision
  have hbandNarrowSelected : (1 / 8 : ENNReal) * band.band.mass ≤
      selected.mass := by
    calc
      (1 / 8 : ENNReal) * band.band.mass =
          (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * band.band.mass) := by
        have hmul : (4 : ENNReal) * 2 = 8 := by norm_num
        have hinv : ((4 : ENNReal) * 2)⁻¹ =
            (4 : ENNReal)⁻¹ * 2⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [show (1 / 8 : ENNReal) = (1 / 4) * (1 / 2) by
          simpa [one_div, hmul] using hinv]
        ring
      _ ≤ (1 / 4 : ENNReal) * narrow.shading.mass := by
        exact mul_le_mul_left' narrow.mass_lower _
      _ ≤ selected.mass := hselectedMass
  have hmass : (1 / 16 : ENNReal) * source.mass ≤
      bandCount * selected.mass := by
    have hhalfHigh := mul_le_mul_left' hhighMass (1 / 8 : ENNReal)
    calc
      (1 / 16 : ENNReal) * source.mass =
          (1 / 8 : ENNReal) * ((1 / 2 : ENNReal) * source.mass) := by
        have hmul : (8 : ENNReal) * 2 = 16 := by norm_num
        have hinv : ((8 : ENNReal) * 2)⁻¹ =
            (8 : ENNReal)⁻¹ * 2⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [show (1 / 16 : ENNReal) = (1 / 8) * (1 / 2) by
          simpa [one_div, hmul] using hinv]
        ring
      _ ≤ (1 / 8 : ENNReal) * high.mass := hhalfHigh
      _ ≤ (1 / 8 : ENNReal) * (bandCount * band.band.mass) := by gcongr
      _ = bandCount * ((1 / 8 : ENNReal) * band.band.mass) := by ring
      _ ≤ bandCount * selected.mass := by gcongr
  let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
    paperWeakPlaneMapMono hincidence weakMap
  let massLoss := proposition63Lemma43MassLoss (1 / 16) bandCount
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top (by norm_num) hbandCountTop
  have hinverse : massLoss⁻¹ * source.mass ≤ selected.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      (by norm_num) (by norm_num) hbandCountTop hmass
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family selected := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal hselectedSource
      hinverse hselectedCubical hsourceTarget
    · simpa [massLoss, bandCount, proposition63PaperLemma43MassLoss]
        using hrestore high band
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  exact ⟨{
    shading := selected
    subshading := hselectedSource
    cubical := hselectedCubical
    planeMap := finalMap
    leftFactor := 1 / 16
    rightFactor := bandCount
    leftFactor_pos := by norm_num
    leftFactor_ne_top := by norm_num
    rightFactor_ne_top := hbandCountTop
    mass_retention := hmass
    extremal := hextremal
  }⟩

/-- Apply precisely the analogue of [16, Lemma 4.3] to one supplied cropped
extremal pair.  The two explicit slack hypotheses are the paper's parameter-
hierarchy absorption in the dense and sparse branches respectively. -/
theorem proposition63_lemma43_weak_plane_map
    {delta sigma sourceLoss targetLoss densityLoss kappa
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta sourceLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * sourceLoss))
    (hkappa : 0 < kappa)
    (hdenseIncidence : kappa ≤ incidenceBudget)
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) source
      (Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss)),
        Nonempty (SparseRelativeBandCVPackage source prepared))
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) source
      (Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss)),
        ∀ package : SparseRelativeBandCVPackage source prepared,
          package.tau / kappa ≤ incidenceBudget)
    (hdenseSlack :
      proposition63Lemma43DenseMassLoss delta sigma sourceLoss *
          Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta sourceLoss)
    (hsparseSlack : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) source
      (Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss)),
        proposition63Lemma43SparseMassLoss prepared *
            Kakeya.realRpowENN delta targetLoss ≤
          Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  subst densityLoss
  rcases high_multiplicity_balanced_direction_dichotomy
      sourceExtremal hline hdeltaSmall rfl hsourceLoss hsmall
      hfixedAbsorb with ⟨dichotomy⟩
  cases dichotomy with
  | dense m R high denseCells selected center planeMap R_def R_pos budget
      upper_budget density_lower high_subshading dense_subshading
      selected_subshading selected_cubical center_measurable cluster
      center_cellwise planeMap_cellwise coordination_density mass_retention =>
      let leftFactor :=
        proposition63Lemma43DenseLeftFactor delta sigma sourceLoss
      have hdensityPos : 0 < Kakeya.realRpowENN delta
          (2 - sigma + 3 * sourceLoss) := by
        simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos sourceExtremal.delta_pos]
      have hleftPos : 0 < leftFactor := by
        dsimp only [leftFactor, proposition63Lemma43DenseLeftFactor]
        exact ENNReal.mul_pos
          (ENNReal.div_pos hdensityPos.ne' (by norm_num)).ne'
          (by norm_num)
      have hleftTop : leftFactor ≠ ⊤ := by
        dsimp only [leftFactor, proposition63Lemma43DenseLeftFactor]
        exact ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by simp [Kakeya.realRpowENN]) (by norm_num))
          (by norm_num)
      have hmass : leftFactor * source.mass ≤
          (2 : ENNReal) * selected.mass := by
        simpa [leftFactor, proposition63Lemma43DenseLeftFactor, mul_assoc]
          using mass_retention
      let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
        paperWeakPlaneMapMono hdenseIncidence planeMap
      have hinverse :
          (proposition63Lemma43MassLoss leftFactor 2)⁻¹ * source.mass ≤
            selected.mass :=
        proposition63Lemma43MassLoss_inv_mul_le
          hleftPos hleftTop (by norm_num) hmass
      have hextremal : WZ2PaperCroppedIsExtremal
          sigma targetLoss family selected := by
        apply transfer_cropped_extremal_to_subshading
          (proposition63Lemma43MassLoss leftFactor 2)
          (proposition63Lemma43MassLoss_pos _ _)
          (proposition63Lemma43MassLoss_ne_top hleftPos (by norm_num))
          sourceExtremal
          (fun index => (selected_subshading index).trans <|
            (dense_subshading index).trans (high_subshading index))
          hinverse selected_cubical hsourceTarget
        · simpa [leftFactor, proposition63Lemma43DenseMassLoss] using
            hdenseSlack
        · exact sourceExtremal.delta_pos
        · exact sourceExtremal.delta_le_one
        · exact htargetLoss
      exact ⟨{
        shading := selected
        subshading := fun index => (selected_subshading index).trans <|
          (dense_subshading index).trans (high_subshading index)
        cubical := selected_cubical
        planeMap := finalMap
        leftFactor := leftFactor
        rightFactor := 2
        leftFactor_pos := hleftPos
        leftFactor_ne_top := hleftTop
        rightFactor_ne_top := by norm_num
        mass_retention := hmass
        extremal := hextremal
      }⟩
  | sparse m R high sparseCells R_def R_pos budget upper_budget density_lower
      coordination_density high_subshading sparse_subshading sparse_cubical
      multiplicity_lower close_count mass_retention =>
      let densityPower :=
        Kakeya.realRpowENN delta (2 - sigma + 3 * sourceLoss)
      have hsparseSub : PaperIsSubshading sparseCells source := fun index =>
        (sparse_subshading index).trans (high_subshading index)
      rcases sparse_relative_band_preparation densityPower m R (by omega)
          R_pos budget upper_budget hsparseSub sparse_cubical
          multiplicity_lower close_count (by
            simpa [densityPower] using density_lower) mass_retention with
        ⟨prepared⟩
      rcases hsparsePackage prepared with ⟨package⟩
      let M := prepared.multiplicity
      let Q := M ^ 3 / 4
      have hM : 0 < M := by
        rw [show M = 2 ^ prepared.level by
          exact prepared.multiplicity_eq]
        positivity
      have hQpos : 0 < Q := by
        dsimp only [Q]
        have hcube : 4 ≤ M ^ 3 := by
          have hMR : 12 * prepared.closeThreshold ≤ M :=
            prepared.combinatorial_budget
          have hR : 0 < prepared.closeThreshold :=
            prepared.closeThreshold_pos
          have htwo : 2 ≤ M := by omega
          calc
            4 ≤ 2 ^ 3 := by norm_num
            _ ≤ M ^ 3 := Nat.pow_le_pow_left htwo 3
        exact Nat.div_pos hcube (by norm_num)
      have hQ : 4 * Q ≤ M ^ 3 := by
        dsimp only [Q]
        exact Nat.mul_div_le (M ^ 3) 4
      have hmultiplicityUpper : ∀ point ∈ prepared.shading.union,
          (prepared.shading.pointMultiplicity point : ENNReal) ≤
            (2 * M : ℕ) := by
        intro point hpoint
        exact_mod_cast (prepared.multiplicity_upper point hpoint).le
      have hbroadSmall :
          2 * (∫⁻ point in paperCountedBroadSet prepared.shading
              package.tau Q,
            (prepared.shading.pointMultiplicity point : ENNReal)) ≤
              prepared.shading.mass := by
        exact paper_broad_mass_budget_main package.coefficient package.cv
          (2 * M : ℕ) hmultiplicityUpper Q package.tau hQpos
          package.tau_pos (by simpa [Q, M] using package.absorb)
      have hbroadMeasurable : MeasurableSet
          (paperCountedBroadSet prepared.shading package.tau Q) :=
        paperCountedBroadSet_measurable prepared.shading package.tau Q
      rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with
        ⟨narrow⟩
      have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
          point ∈ narrow.shading.carrier index →
            paperCloseDirectionCount narrow.shading point index kappa <
              prepared.closeThreshold := by
        intro point hpoint index hindex
        have hpointPrepared : point ∈ prepared.shading.union :=
          ⟨index, narrow.subshading index hindex⟩
        have hmono : paperCloseDirectionCount narrow.shading point index
            kappa ≤ paperCloseDirectionCount prepared.shading point index
              kappa := by
          unfold paperCloseDirectionCount
          apply Finset.card_le_card
          intro other hother
          simp only [Finset.mem_filter] at hother ⊢
          exact ⟨hother.1, narrow.subshading other hother.2.1, hother.2.2⟩
        exact hmono.trans_lt <| prepared.close_count point hpointPrepared
          index (narrow.subshading index hindex)
      have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
          narrow.shading.pointMultiplicity point =
            prepared.shading.pointMultiplicity point :=
        fun point hpoint => paper_narrow_pointMultiplicity_eq narrow hpoint
      have hnarrowBudget : ∀ point ∈ narrow.shading.union,
          let mu := narrow.shading.pointMultiplicity point
          4 * (Q + 3 * prepared.closeThreshold * mu ^ 2) ≤
            3 * mu ^ 3 := by
        intro point hpoint
        have hmultiplicity : M ≤ narrow.shading.pointMultiplicity point := by
          rw [hnarrowMultiplicity point hpoint]
          have hpointPrepared : point ∈ prepared.shading.union := by
            rcases hpoint with ⟨index, hindex⟩
            exact ⟨index, narrow.subshading index hindex⟩
          exact prepared.multiplicity_lower point hpointPrepared
        exact wz1_good_triple_budget M Q prepared.closeThreshold
          (narrow.shading.pointMultiplicity point) hmultiplicity hQ
          prepared.combinatorial_budget
      rcases paper_cellwise_weak_planiness_from_narrow
          sourceExtremal.delta_pos hkappa sourceExtremal.nonempty
          prepared.cubical narrow hnarrowClose hnarrowBudget with
        ⟨selected, _selection, planeMap, hselectedSub, hselectedCubical,
          hplaneCell, _hselectionCell, _hplaneSelection,
          _hnarrowMultiplicityUpper, hselectedMass⟩
      have hselectedSource : PaperIsSubshading selected source := fun index =>
        (hselectedSub index).trans <|
          (narrow.subshading index).trans <|
            (prepared.subshading index).trans
              (prepared.source_subshading index)
      have hmass : (1 / 32 : ENNReal) * source.mass ≤
          (prepared.bandCount : ENNReal) * selected.mass := by
        have hscaledPrepared := mul_le_mul_left' prepared.mass_retention
          (1 / 8 : ENNReal)
        have hquarterNarrow :
            (1 / 8 : ENNReal) * prepared.shading.mass ≤
              (1 / 4 : ENNReal) * narrow.shading.mass := by
          have heighth : (1 / 8 : ENNReal) = (1 / 4) * (1 / 2) := by
            have hmul : (4 : ENNReal) * 2 = 8 := by norm_num
            have hinv : ((4 : ENNReal) * 2)⁻¹ =
                (4 : ENNReal)⁻¹ * 2⁻¹ := by
              rw [ENNReal.mul_inv] <;> norm_num
            simpa [one_div, hmul] using hinv
          calc
            (1 / 8 : ENNReal) * prepared.shading.mass =
                (1 / 4 : ENNReal) *
                  ((1 / 2 : ENNReal) * prepared.shading.mass) := by
                    rw [heighth]
                    ring
            _ ≤ (1 / 4 : ENNReal) * narrow.shading.mass := by
              exact mul_le_mul_left' narrow.mass_lower _
        calc
          (1 / 32 : ENNReal) * source.mass =
              (1 / 8 : ENNReal) * ((1 / 4 : ENNReal) * source.mass) := by
                have hmul : (8 : ENNReal) * 4 = 32 := by norm_num
                have hinv : ((8 : ENNReal) * 4)⁻¹ =
                    (8 : ENNReal)⁻¹ * 4⁻¹ := by
                  rw [ENNReal.mul_inv] <;> norm_num
                rw [show (1 / 32 : ENNReal) =
                  (1 / 8) * (1 / 4) by
                    simpa [one_div, hmul] using hinv]
                ring
          _ ≤ (1 / 8 : ENNReal) *
              ((prepared.bandCount : ENNReal) * prepared.shading.mass) :=
                hscaledPrepared
          _ = (prepared.bandCount : ENNReal) *
              ((1 / 8 : ENNReal) * prepared.shading.mass) := by ring
          _ ≤ (prepared.bandCount : ENNReal) *
              ((1 / 4 : ENNReal) * narrow.shading.mass) := by
                exact mul_le_mul_left' hquarterNarrow _
          _ ≤ (prepared.bandCount : ENNReal) * selected.mass :=
                mul_le_mul_left' hselectedMass _
      let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
        paperWeakPlaneMapMono (hsparseIncidence prepared package) planeMap
      have hinverse :
          (proposition63Lemma43MassLoss (1 / 32) prepared.bandCount)⁻¹ *
              source.mass ≤ selected.mass :=
        proposition63Lemma43MassLoss_inv_mul_le
          (by norm_num) (by norm_num) (by simp) hmass
      have hextremal : WZ2PaperCroppedIsExtremal
          sigma targetLoss family selected := by
        apply transfer_cropped_extremal_to_subshading
          (proposition63Lemma43MassLoss (1 / 32) prepared.bandCount)
          (proposition63Lemma43MassLoss_pos _ _)
          (proposition63Lemma43MassLoss_ne_top (by norm_num) (by simp))
          sourceExtremal hselectedSource hinverse hselectedCubical
          hsourceTarget
        · simpa [proposition63Lemma43SparseMassLoss] using
            hsparseSlack prepared
        · exact sourceExtremal.delta_pos
        · exact sourceExtremal.delta_le_one
        · exact htargetLoss
      exact ⟨{
        shading := selected
        subshading := hselectedSource
        cubical := hselectedCubical
        planeMap := finalMap
        leftFactor := 1 / 32
        rightFactor := prepared.bandCount
        leftFactor_pos := by norm_num
        leftFactor_ne_top := by norm_num
        rightFactor_ne_top := by simp
        mass_retention := hmass
        extremal := hextremal
      }⟩

end Kakeya.Assouad.PureWZ2

end
