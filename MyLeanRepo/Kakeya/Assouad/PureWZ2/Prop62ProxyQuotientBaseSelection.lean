import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentWeight
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62GlobalUpperEnvelopeParentSelection
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient base selection

The first geometric selection is exactly the global residue/per-cell
upper-color selection.  Its weighted retention yields positive selected
weight, hence the nonemptiness required before constructing the metric.

After the metric has been constructed, the same actual selection supplies
the base stage of the mass ledger.  Its exact loss is the residue cardinality
times the proxy upper-color-vector cardinality.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62GlobalResiduePerCellSelectionData

variable
    {Index Cell Residue Color : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Cell] [DecidableEq Cell]
    [Fintype Residue] [DecidableEq Residue] [Nonempty Residue]
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {cell : Index → Cell}
    {residue : Index → Residue}
    {color : Index → Color}
    {weight : Index → ENNReal}
    (selection :
      PureWZ2Prop62GlobalResiduePerCellSelectionData
        Index Cell Residue Color cell residue color weight)

theorem selectionWeightPos_of_totalWeightPos
    (totalWeightPos :
      0 < ∑ index : Index, weight index) :
    0 < ∑ index ∈ selection.selected, weight index := by
  by_contra selectedNotPos
  have selectedZero :
      (∑ index ∈ selection.selected, weight index) = 0 :=
    bot_unique (not_lt.mp selectedNotPos)
  have totalLeZero :
      (∑ index : Index, weight index) ≤ 0 := by
    simpa [selectedZero] using selection.weight_retention
  exact (not_le_of_gt totalWeightPos) totalLeZero

theorem selected_nonempty_of_totalWeightPos
    (totalWeightPos :
      0 < ∑ index : Index, weight index) :
    selection.selected.Nonempty := by
  have selectedWeightPos :=
    selection.selectionWeightPos_of_totalWeightPos totalWeightPos
  by_contra selectedEmpty
  have selectedEq : selection.selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp selectedEmpty
  rw [selectedEq] at selectedWeightPos
  simp at selectedWeightPos

end PureWZ2Prop62GlobalResiduePerCellSelectionData

theorem pureWZ2Prop62_weight_ne_top_of_totalWeight_ne_top
    {Index : Type*}
    [Fintype Index]
    {weight : Index → ENNReal}
    (totalWeightFinite :
      (∑ index : Index, weight index) ≠ ⊤)
    (index : Index) :
    weight index ≠ ⊤ := by
  apply ne_top_of_le_ne_top totalWeightFinite
  exact
    Finset.single_le_sum
      (fun _ _ => bot_le)
      (Finset.mem_univ index)

theorem pureWZ2Prop62_weight_sum_eq_sourceShading_mass
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (weight : Fin fine.card → ENNReal)
    (weightEq :
      ∀ source, weight source = volume (shading.carrier source)) :
    (∑ source : Fin fine.card, weight source) = shading.mass := by
  apply Finset.sum_congr rfl
  intro source _
  exact weightEq source

def pureWZ2Prop62ProxyQuotientBaseSelectionLoss
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ) : ENNReal :=
  (Fintype.card (Fin 4 → ZMod (strideBase + 1)) : ENNReal) *
    (Fintype.card
      (schedule.ProxyUpperColorVector rho packetCoordinate) : ENNReal)

def pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
    (depthBound strideBaseBound : ℕ) : ENNReal :=
  ((strideBaseBound + 1 : ℕ) : ENNReal) ^ 4 *
    ((pureWZ2Prop62ProxyCenterConflictDegree + 1 : ℕ) :
      ENNReal) ^ depthBound

theorem pureWZ2Prop62ProxyQuotientBaseSelectionLoss_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ) :
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss
        schedule rho packetCoordinate strideBase =
      ((strideBase + 1 : ℕ) : ENNReal) ^ 4 *
        ((pureWZ2Prop62ProxyCenterConflictDegree + 1 : ℕ) :
          ENNReal) ^
          Fintype.card
            (schedule.ProxyUpperCoordinate rho packetCoordinate) := by
  unfold pureWZ2Prop62ProxyQuotientBaseSelectionLoss
  norm_cast
  simp [Fintype.card_pi]

theorem pureWZ2Prop62ProxyQuotientBaseSelectionLoss_ne_top
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (rho : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ) :
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss
        schedule rho packetCoordinate strideBase ≠ ⊤ := by
  rw [pureWZ2Prop62ProxyQuotientBaseSelectionLoss_eq]
  exact
    ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem pureWZ2Prop62ProxyQuotientBaseSelectionLoss_le_fixedBound
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase depthBound strideBaseBound : ℕ)
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe : strideBase ≤ strideBaseBound) :
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss
        schedule rho packetCoordinate strideBase ≤
      pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
        depthBound strideBaseBound := by
  rw [pureWZ2Prop62ProxyQuotientBaseSelectionLoss_eq]
  unfold pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
  exact_mod_cast
    Nat.mul_le_mul
      (Nat.pow_le_pow_left (by omega) 4)
      (Nat.pow_le_pow_right (by positivity) <|
        (pureWZ2Prop62_proxyUpperCoordinate_card_le_levelCount
          schedule packetCoordinate).trans depthLe)

theorem pureWZ2_prop62_proxy_quotient_selectionWeightPos
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (totalWeightPos :
      0 < ∑ source : Fin fine.card, weight source) :
    0 <
      ∑ source ∈
          (quotient.selectProxyResidueUpperAncestryPerCell
            rho width packetCoordinate strideBase weight).selected,
        weight source :=
  (quotient.selectProxyResidueUpperAncestryPerCell
    rho width packetCoordinate strideBase weight
    ).selectionWeightPos_of_totalWeightPos totalWeightPos

theorem pureWZ2_prop62_proxy_quotient_selection_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (totalWeightPos :
      0 < ∑ source : Fin fine.card, weight source) :
    (quotient.selectProxyResidueUpperAncestryPerCell
      rho width packetCoordinate strideBase weight).selected.Nonempty :=
  (quotient.selectProxyResidueUpperAncestryPerCell
    rho width packetCoordinate strideBase weight
    ).selected_nonempty_of_totalWeightPos totalWeightPos

structure PureWZ2Prop62ProxyQuotientBaseSelectionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight) where
  selectionWeightPos :
    0 < ∑ source ∈ metric.selection.selected, weight source
  selection_nonempty :
    metric.selection.selected.Nonempty
  weight_finite :
    ∀ source : Fin fine.card, weight source ≠ ⊤
  baseSelectedParents :
    Finset (Fin metric.metricParents.card)
  baseSelectedParents_eq :
    baseSelectedParents = Finset.univ
  baseSelectionLoss : ENNReal
  baseSelectionLoss_eq :
    baseSelectionLoss =
      pureWZ2Prop62ProxyQuotientBaseSelectionLoss
        schedule rho packetCoordinate strideBase
  baseSelectionLoss_ne_top :
    baseSelectionLoss ≠ ⊤
  base_selection_retention :
    (∑ source : Fin fine.card, weight source) ≤
      baseSelectionLoss *
        ∑ parent ∈ baseSelectedParents,
          metric.metricParentWeight parent

noncomputable def pureWZ2_prop62_proxy_quotient_base_selection
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (totalWeightPos :
      0 < ∑ source : Fin fine.card, weight source)
    (totalWeightFinite :
      (∑ source : Fin fine.card, weight source) ≠ ⊤) :
    PureWZ2Prop62ProxyQuotientBaseSelectionData
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric := by
  let baseSelectionLoss :=
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss
      schedule rho packetCoordinate strideBase
  have selectionWeightPos :
      0 < ∑ source ∈ metric.selection.selected, weight source :=
    metric.selection.selectionWeightPos_of_totalWeightPos
      totalWeightPos
  have baseRetention :
      (∑ source : Fin fine.card, weight source) ≤
        baseSelectionLoss *
          ∑ parent ∈
              (Finset.univ :
                Finset (Fin metric.metricParents.card)),
            metric.metricParentWeight parent := by
    calc
      (∑ source : Fin fine.card, weight source) ≤
          baseSelectionLoss *
            ∑ source ∈ metric.selection.selected, weight source := by
        simpa only [baseSelectionLoss,
          pureWZ2Prop62ProxyQuotientBaseSelectionLoss] using
            metric.selection.weight_retention
      _ =
          baseSelectionLoss *
            ∑ parent ∈
                (Finset.univ :
                  Finset (Fin metric.metricParents.card)),
              metric.metricParentWeight parent := by
        rw [← metric.sum_metricParentWeight_eq_selection]
  exact
    {
      selectionWeightPos := selectionWeightPos
      selection_nonempty :=
        metric.selection.selected_nonempty_of_totalWeightPos
          totalWeightPos
      weight_finite :=
        pureWZ2Prop62_weight_ne_top_of_totalWeight_ne_top
          totalWeightFinite
      baseSelectedParents := Finset.univ
      baseSelectedParents_eq := rfl
      baseSelectionLoss := baseSelectionLoss
      baseSelectionLoss_eq := rfl
      baseSelectionLoss_ne_top :=
        pureWZ2Prop62ProxyQuotientBaseSelectionLoss_ne_top
          schedule rho packetCoordinate strideBase
      base_selection_retention := baseRetention
    }

noncomputable def pureWZ2_prop62_proxy_quotient_base_selection_of_shading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (shading : WZ1PaperTubeShading fine)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (weightEq :
      ∀ source, weight source = volume (shading.carrier source))
    (sourceMassPos : 0 < shading.mass)
    (sourceMassFinite : shading.mass ≠ ⊤) :
    PureWZ2Prop62ProxyQuotientBaseSelectionData
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric := by
  have totalWeightEq :
      (∑ source : Fin fine.card, weight source) = shading.mass :=
    pureWZ2Prop62_weight_sum_eq_sourceShading_mass
      shading weight weightEq
  exact
    pureWZ2_prop62_proxy_quotient_base_selection
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric
        (by rwa [totalWeightEq])
        (by rwa [totalWeightEq])

namespace PureWZ2Prop62ProxyQuotientBaseSelectionData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    (data :
      PureWZ2Prop62ProxyQuotientBaseSelectionData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric)

theorem baseSelectionLoss_formula :
    data.baseSelectionLoss =
      ((strideBase + 1 : ℕ) : ENNReal) ^ 4 *
        ((pureWZ2Prop62ProxyCenterConflictDegree + 1 : ℕ) :
          ENNReal) ^
          Fintype.card
            (schedule.ProxyUpperCoordinate rho packetCoordinate) := by
  rw [data.baseSelectionLoss_eq,
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss_eq]

theorem baseSelectionLoss_le_fixedBound
    {depthBound strideBaseBound : ℕ}
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe : strideBase ≤ strideBaseBound) :
    data.baseSelectionLoss ≤
      pureWZ2Prop62ProxyQuotientBaseSelectionFixedBound
        depthBound strideBaseBound := by
  rw [data.baseSelectionLoss_eq]
  exact
    pureWZ2Prop62ProxyQuotientBaseSelectionLoss_le_fixedBound
      schedule packetCoordinate strideBase depthBound
        strideBaseBound depthLe strideLe

end PureWZ2Prop62ProxyQuotientBaseSelectionData

end Kakeya.Assouad

end
