import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityDirectionInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountCWA

/-!
# Property (P) from cropped CWA and a high-multiplicity restriction

This is the second-planiness input used after the Proposition 6.3
normalization.  The high-multiplicity threshold carries the ambient family
cardinality, while the cropped CWA close-direction estimate has the same
factor.  Comparing the two before selecting transverse partners avoids both
a historical full-line distinctness hypothesis and an artificial cardinality
upper bound.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Package an already selected whole-cell high-multiplicity shading as
Property (P), using a strict ambient close-direction count. -/
def propertyP_of_high_multiplicity_close_count
    {sigma sourceLoss L tau epsilon₁ epsilon₃ kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    {source propertyOne : WZ1PaperTubeShading family}
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceLoss family source)
    (hpropertySub : PaperIsSubshading propertyOne source)
    (hpropertyMass :
      (1 / 2 : ENNReal) * source.mass ≤ propertyOne.mass)
    (hpropertyCubical : WZ1PaperIsCubicalShading propertyOne)
    (hpropertyCommon : ∀ index, propertyOne.carrier index =
      source.carrier index ∩ propertyOne.union)
    (m : ℕ)
    (hmPos : 0 < m)
    (hmPacking :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal))
    (hmultiplicity : ∀ point ∈ propertyOne.union,
      m ≤ propertyOne.pointMultiplicity point)
    (hclose : ∀ point, point ∈ source.union →
      ∀ index, point ∈ source.carrier index →
        (paperCloseDirectionCount source point index kappa : ENNReal) <
          (m : ENNReal))
    (hline : WZ1PaperIsLineClass family)
    (hL : 0 < L)
    (htau : 0 < tau)
    (htauLarge : L * Real.sqrt 3 ≤ tau)
    (hcell :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        Kakeya.realRpowENN L 3)
    (hkappa : Real.rpow L epsilon₃ ≤ kappa) :
    PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := source) epsilon₁ epsilon₃ := by
  have hfull : ∀ index point, point ∈ propertyOne.carrier index →
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        volume (propertyOne.carrier index ∩ Metric.closedBall point tau) := by
    intro index point hpoint
    let cell := wz1PaperGridIndex L point
    let cube := wz1PaperGridCube L cell
    have hpointCube : point ∈ cube := by
      rw [mem_wz1PaperGridCube]
    have hcubeCarrier : cube ⊆ propertyOne.carrier index :=
      hpropertyCubical index point hpoint
    have hcubeBall : cube ⊆ Metric.closedBall point tau := by
      intro other hother
      have hpointBox : point ∈ {value : Point3 |
          (cell.1 : ℝ) * L ≤ value 0 ∧
          value 0 < ((cell.1 : ℝ) + 1) * L ∧
          (cell.2.1 : ℝ) * L ≤ value 1 ∧
          value 1 < ((cell.2.1 : ℝ) + 1) * L ∧
          (cell.2.2 : ℝ) * L ≤ value 2 ∧
          value 2 < ((cell.2.2 : ℝ) + 1) * L} := by
        rwa [← wz1PaperGridCube_eq_Ico hL cell]
      have hotherBox : other ∈ {value : Point3 |
          (cell.1 : ℝ) * L ≤ value 0 ∧
          value 0 < ((cell.1 : ℝ) + 1) * L ∧
          (cell.2.1 : ℝ) * L ≤ value 1 ∧
          value 1 < ((cell.2.1 : ℝ) + 1) * L ∧
          (cell.2.2 : ℝ) * L ≤ value 2 ∧
          value 2 < ((cell.2.2 : ℝ) + 1) * L} := by
        rwa [← wz1PaperGridCube_eq_Ico hL cell]
      have hcoordinate : ∀ coordinate : Fin 3,
          |other coordinate - point coordinate| < L := by
        intro coordinate
        fin_cases coordinate <;> simp [abs_lt] <;> constructor <;>
          rcases hpointBox with ⟨hp0l, hp0u, hp1l, hp1u, hp2l, hp2u⟩ <;>
          rcases hotherBox with ⟨ho0l, ho0u, ho1l, ho1u, ho2l, ho2u⟩ <;>
          linarith
      have hnormSq : dist other point ^ 2 =
          ∑ coordinate : Fin 3,
            (other coordinate - point coordinate) ^ 2 := by
        rw [dist_eq_norm]
        exact EuclideanSpace.real_norm_sq_eq (other - point)
      have hsum : (∑ coordinate : Fin 3,
          (other coordinate - point coordinate) ^ 2) < 3 * L ^ 2 := by
        rw [show (∑ coordinate : Fin 3,
            (other coordinate - point coordinate) ^ 2) =
          (other 0 - point 0) ^ 2 + (other 1 - point 1) ^ 2 +
            (other 2 - point 2) ^ 2 by
              simp [Fin.sum_univ_succ] <;> ring]
        have h0 := hcoordinate 0
        have h1 := hcoordinate 1
        have h2 := hcoordinate 2
        nlinarith [abs_lt.mp h0, abs_lt.mp h1, abs_lt.mp h2]
      have hdist : dist other point < L * Real.sqrt 3 := by
        have hsqrt : (L * Real.sqrt 3) ^ 2 = 3 * L ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num)]
          ring
        have hnonnegative : 0 ≤ dist other point := dist_nonneg
        have hright : 0 ≤ L * Real.sqrt 3 := by positivity
        nlinarith [hnormSq, hsum, hsqrt]
      exact hdist.le.trans htauLarge
    have hcube : cube ⊆
        propertyOne.carrier index ∩ Metric.closedBall point tau :=
      fun other hother => ⟨hcubeCarrier hother, hcubeBall hother⟩
    calc
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
          Kakeya.realRpowENN L 3 := hcell
      _ = volume cube := by
        have htranslate : volume cube =
            volume (wz1PaperGridCube L (0, 0, 0)) :=
          wz1PaperGridCube_volume_eq hL cell (0, 0, 0)
        have hvolume : volume cube = ENNReal.ofReal (L ^ 3) := by
          rw [htranslate]
          exact wz1PaperGridCube_volume_exact hL
        rw [hvolume]
        simp [Kakeya.realRpowENN, Real.rpow_natCast]
      _ ≤ volume
          (propertyOne.carrier index ∩ Metric.closedBall point tau) :=
        measure_mono hcube
  have htransverse : ∀ point ∈ propertyOne.union,
      ∀ index, point ∈ propertyOne.carrier index →
        ∃ other, point ∈ propertyOne.carrier other ∧
          Real.rpow L epsilon₃ ≤
            ‖wz1Cross (family.tube index).direction
              (family.tube other).direction‖ := by
    intro point hpoint index hindex
    have hsourcePoint : point ∈ source.union := by
      rcases hpoint with ⟨sourceIndex, hsourceIndex⟩
      exact ⟨sourceIndex, hpropertySub sourceIndex hsourceIndex⟩
    have hsourceIndex : point ∈ source.carrier index :=
      hpropertySub index hindex
    rcases paperTransverseFromCloseCountLtMultiplicity
        point hpoint (hmultiplicity point hpoint) hpropertySub index kappa
        (hclose point hsourcePoint index hsourceIndex) with
      ⟨other, hother, hseparation⟩
    exact ⟨other, hother, hkappa.trans hseparation⟩
  exact
    { propertyOne := propertyOne
      propertyOne_sub := hpropertySub
      propertyOne_mass := hpropertyMass
      propertyThree := propertyOne
      propertyThree_sub := fun _ => Set.Subset.rfl
      propertyThree_common_spatial := by
        exact hpropertyCommon
      propertyThree_mass := hpropertyMass
      propertyThree_cubical := hpropertyCubical
      multiplicity := m
      multiplicity_pos := hmPos
      multiplicity_lower_pointwise := hmultiplicity
      multiplicity_gt_packing := hmPacking
      propertyOne_full := hfull
      transverse := htransverse }

/-- Cropped CWA and the high-multiplicity threshold have the same ambient
cardinality factor.  Once their scalar coefficients are separated, the
resulting whole-cell shading satisfies Property (P). -/
theorem propertyP_refinement_of_cwa
    {sigma sourceLoss densityLoss L tau epsilon₁ epsilon₃ kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hCWA : WZ2PaperConvexWolffBound family C)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (hsmall : Kakeya.realRpowENN L sourceLoss < 1 / 4)
    (hLsmall24 : L ≤ 1 / 24)
    (hLsmall10000 : L ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN L (-sigma + 4 * sourceLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau)
    (hLtau : L ≤ tau)
    (htauLarge : L * Real.sqrt 3 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * L)
    (htauOne : tau ≤ 1)
    (hcell :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        Kakeya.realRpowENN L 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaL : L ≤ kappa)
    (hkappaProperty : Real.rpow L epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard <
        Kakeya.realRpowENN L densityLoss * family.enncard) :
    Nonempty (PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := source) epsilon₁ epsilon₃) := by
  rcases high_multiplicity_direction_input sourceExtremal hline hLsmall24
      hdensityLoss hsourceLoss hsmall with
    ⟨m, selected, hselectedSub, hselectedCubical, hmultiplicity,
      hmLower, hselectedMass, hselectedCommon, hmPos⟩
  have hmPacking :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal) := by
    have hsucc :
        ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal) ≤
          (m : ENNReal) :=
      (density_power_cardinality_ge_fixed sourceExtremal
        ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)
        hLsmall24 hdensityLoss hpackingAbsorb).trans hmLower
    exact_mod_cast (show
      2 * 4 * 601 ^ 3 * 12001 ^ 3 < m by
        have : 2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 ≤ m := by
          exact_mod_cast hsucc
        omega)
  have hclose : ∀ point, point ∈ source.union →
      ∀ index, point ∈ source.carrier index →
        (paperCloseDirectionCount source point index kappa : ENNReal) <
          (m : ENNReal) := by
    intro point _hpoint index hpoint
    have hcount := paper_cwa_close_direction_count hCWA
      sourceExtremal.delta_pos hLsmall10000 kappa
      hkappa hkappaOne hkappaL point index hpoint
    have hcoefficient :
        C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard <
          (m : ENNReal) := hcloseAbsorb.trans_le hmLower
    exact hcount.trans_lt hcoefficient
  exact ⟨propertyP_of_high_multiplicity_close_count sourceExtremal
    hselectedSub hselectedMass hselectedCubical hselectedCommon m hmPos hmPacking
    hmultiplicity hclose hline sourceExtremal.delta_pos htau htauLarge
    hcell hkappaProperty⟩

/-- The concrete CWA construction uses the same whole-cell shading for
Property One and Property Three.  Exposing that equality lets downstream
HIGH covering arguments reuse `propertyOne_full` without adding a separate
fullness hypothesis. -/
theorem propertyP_refinement_of_cwa_eq
    {sigma sourceLoss densityLoss L tau epsilon₁ epsilon₃ kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hCWA : WZ2PaperConvexWolffBound family C)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (hsmall : Kakeya.realRpowENN L sourceLoss < 1 / 4)
    (hLsmall24 : L ≤ 1 / 24)
    (hLsmall10000 : L ≤ 1 / 10000)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN L (-sigma + 4 * sourceLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau)
    (hLtau : L ≤ tau)
    (htauLarge : L * Real.sqrt 3 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * L)
    (htauOne : tau ≤ 1)
    (hcell :
      Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        Kakeya.realRpowENN L 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaL : L ≤ kappa)
    (hkappaProperty : Real.rpow L epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard <
        Kakeya.realRpowENN L densityLoss * family.enncard) :
    ∃ propP : PureWZ2PropertyPData
        (sigma := sigma) (L := L) (tau := tau)
        (coarseShading := source) epsilon₁ epsilon₃,
      propP.propertyThree = propP.propertyOne := by
  rcases high_multiplicity_direction_input sourceExtremal hline hLsmall24
      hdensityLoss hsourceLoss hsmall with
    ⟨m, selected, hselectedSub, hselectedCubical, hmultiplicity,
      hmLower, hselectedMass, hselectedCommon, hmPos⟩
  have hmPacking :
      (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal) < (m : ENNReal) := by
    have hsucc :
        ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal) ≤
          (m : ENNReal) :=
      (density_power_cardinality_ge_fixed sourceExtremal
        ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)
        hLsmall24 hdensityLoss hpackingAbsorb).trans hmLower
    exact_mod_cast (show 2 * 4 * 601 ^ 3 * 12001 ^ 3 < m by
      have : 2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 ≤ m := by
        exact_mod_cast hsucc
      omega)
  have hclose : ∀ point, point ∈ source.union →
      ∀ index, point ∈ source.carrier index →
        (paperCloseDirectionCount source point index kappa : ENNReal) <
          (m : ENNReal) := by
    intro point _hpoint index hpoint
    have hcount := paper_cwa_close_direction_count hCWA
      sourceExtremal.delta_pos hLsmall10000 kappa
      hkappa hkappaOne hkappaL point index hpoint
    exact hcount.trans_lt (hcloseAbsorb.trans_le hmLower)
  let propP := propertyP_of_high_multiplicity_close_count sourceExtremal
    hselectedSub hselectedMass hselectedCubical hselectedCommon m hmPos
    hmPacking hmultiplicity hclose hline sourceExtremal.delta_pos htau
    htauLarge hcell hkappaProperty
  exact ⟨propP, rfl⟩

end Kakeya.Assouad.PureWZ2

end
