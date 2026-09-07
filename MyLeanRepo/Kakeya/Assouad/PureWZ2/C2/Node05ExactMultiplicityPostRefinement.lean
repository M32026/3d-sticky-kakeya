import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ReentrantPostRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityRefinement

/-!
# Exact-multiplicity post-refinement receipt for Node 5

This module removes three redundant hypotheses from the reentrant Node-5
post-refinement receipt.  An exact cellwise truncation of the seed fine
shading determines the derived fine refinement, exact multiplicity certificate,
and factor-two band.
After identifying that truncation with the final public shading, the ordinary
balanced cover is upgraded to the Node-5 balanced cover by exact Fubini.

The identification of the two shadings is deliberately heterogeneous: their
tube-family indices are only propositionally related through the stored
selected-subfamily provenance.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Exact point multiplicity and fine-cell nesting upgrade an ordinary
balanced cover to the Node-5 indexed-incidence cover. -/
noncomputable def PureWZ2BalancedCoverData.toNode5OfExactMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (m : ℕ) (hm : 0 < m)
    (hexact : fineShading.HasConstantMultiplicity m m)
    (fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell) :
    PureWZ2Node5BalancedCoverData base where
  incidenceMass := (m : ENNReal) * base.cellMass
  incidenceMass_pos :=
    ENNReal.mul_pos (by simp [Nat.ne_of_gt hm]) base.cellMass_pos.ne'
  incidenceMass_ne_top :=
    ENNReal.mul_ne_top (by simp) base.cellMass_ne_top
  fine_cell_incidence_mass := by
    intro cell hcell
    have hFubini :=
      sum_volume_inter_eq_setLIntegral_pointMultiplicity
        fineShading
        (S := wz1PaperGridCube rho cell)
        (wz1PaperGridCube_measurable cell)
    change (∑ source : Fin (wz1PaperBodyFamily fine).card,
        volume (fineShading.carrier source ∩
          wz1PaperGridCube rho cell)) = (m : ENNReal) * base.cellMass
    rw [hFubini]
    have hpointwise : ∀ point ∈ wz1PaperGridCube rho cell,
        (fineShading.pointMultiplicity point : ENNReal) =
          fineShading.union.indicator
            (fun _ : Point3 => (m : ENNReal)) point := by
      intro point _hpointCell
      by_cases hpointUnion : point ∈ fineShading.union
      · simp only [Set.indicator_of_mem hpointUnion]
        have h := hexact point hpointUnion
        exact_mod_cast le_antisymm h.2 h.1
      · rw [Set.indicator_apply]
        simp only [if_neg hpointUnion]
        have hnone : ∀ source : Fin fine.card,
            point ∉ fineShading.carrier source := by
          intro source hsource
          exact hpointUnion ⟨source, hsource⟩
        simp [Kakeya.Streamlined.Shading.pointMultiplicity, hnone]
    calc
      (∫⁻ point in wz1PaperGridCube rho cell,
          (fineShading.pointMultiplicity point : ENNReal)) =
          ∫⁻ point in wz1PaperGridCube rho cell,
            fineShading.union.indicator
              (fun _ : Point3 => (m : ENNReal)) point := by
            apply MeasureTheory.setLIntegral_congr_fun
              (wz1PaperGridCube_measurable cell)
            exact hpointwise
      _ = ∫⁻ point in fineShading.union ∩ wz1PaperGridCube rho cell,
            (m : ENNReal) := by
          rw [MeasureTheory.setLIntegral_indicator
            (measurableSet_shading_union fineShading)]
      _ = (m : ENNReal) *
            volume (fineShading.union ∩ wz1PaperGridCube rho cell) := by
          rw [MeasureTheory.setLIntegral_const]
      _ = (m : ENNReal) * base.cellMass := by
          rw [base.fine_cell_mass cell hcell]
  fine_cell_nested := fineCellNested

/-- The post-refinement data that remain after exact multiplicity is carried
by an explicit truncation.  In particular, there are no independent fields
for the Node-5 balanced cover or its exact/factor-two multiplicity proofs; the
positive multiplicity value itself remains explicit. -/
structure PureWZ2Node05ExactMultiplicityPostRefinementReceipt
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent) where
  fineRefinementExponent : ℕ
  coarseRefinementExponent : ℕ
  coarseRefinement :
    WZ1PaperRefinement
      seed.data.croppedCoarseShading coarseRefinementExponent
  data :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent
  refined_extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss data.selected.family data.refined
  exactMultiplicity : ℕ
  exactMultiplicity_pos : 0 < exactMultiplicity
  delta_pos : 0 < delta
  truncation :
    PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined delta_pos exactMultiplicity
  refinementScalar :
    2 * wz1PaperRefinementFraction delta fineRefinementExponent ≤ 1
  logExponent_eq :
    logExponent = seedLogExponent + fineRefinementExponent
  selected_eq :
    data.selected = seed.data.selected.comp
      (truncation.toPaperRefinement
        fineRefinementExponent refinementScalar).selected
  refined_eq : HEq data.refined
    (truncation.toPaperRefinement
      fineRefinementExponent refinementScalar).refined
  coarse_eq : data.coarse = coarseRefinement.selected.family
  croppedCoarseShading_eq :
    HEq data.croppedCoarseShading coarseRefinement.refined
  fineCellNested :
    ∀ source point, point ∈ data.refined.carrier source →
      ∃ cell ∈ data.balanced.activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho.1 cell
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.refined.union
  full_fiber_uniform :
    ∀ first second : Fin data.coarse.card,
      ((wz2PaperFullFiberIndices
          data.selected.family data.coarse first).card : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selected.family data.coarse second).card : ENNReal)
  coarse_volume_lower :
    Kakeya.realRpowENN rho.1 (sigma + outputLoss) ≤
      volume data.croppedCoarseShading.union

namespace PureWZ2Node05ExactMultiplicityPostRefinementReceipt

variable
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}
    {seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent}

/-- The exact truncation itself supplies the fine paper refinement. -/
noncomputable def fineRefinement
    (receipt : PureWZ2Node05ExactMultiplicityPostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed) :
    WZ1PaperRefinement seed.data.refined receipt.fineRefinementExponent :=
  receipt.truncation.toPaperRefinement
    receipt.fineRefinementExponent receipt.refinementScalar

/-- Transport a pointwise multiplicity statement along an honest dependent
identification of the two indexed shadings. -/
private theorem constantMultiplicity_of_heq
    {firstFamily secondFamily : Kakeya.Streamlined.TubeFamily delta}
    {first : WZ1PaperTubeShading firstFamily}
    {second : WZ1PaperTubeShading secondFamily}
    {m M : ℕ}
    (hFamily : firstFamily = secondFamily)
    (h : HEq first second)
    (hconstant : first.HasConstantMultiplicity m M) :
    second.HasConstantMultiplicity m M := by
  subst secondFamily
  have hEq : first = second := eq_of_heq h
  subst second
  exact hconstant

/-- Exact multiplicity on the final public shading, obtained solely by
transporting the truncation certificate. -/
theorem final_exact_multiplicity
    (receipt : PureWZ2Node05ExactMultiplicityPostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed) :
    receipt.data.refined.HasConstantMultiplicity
      receipt.exactMultiplicity receipt.exactMultiplicity := by
  have hFamily : seed.data.selected.family = receipt.data.selected.family := by
    rw [receipt.selected_eq]
    rfl
  exact constantMultiplicity_of_heq hFamily receipt.refined_eq.symm
    receipt.truncation.exact_multiplicity

/-- The exact truncation determines the factor-two multiplicity band used by
the public Node-5 interface. -/
theorem final_multiplicity_band
    (receipt : PureWZ2Node05ExactMultiplicityPostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed) :
    receipt.data.refined.HasConstantMultiplicity
      receipt.exactMultiplicity (2 * receipt.exactMultiplicity) := by
  intro point hpoint
  have h := receipt.final_exact_multiplicity point hpoint
  exact ⟨h.1, h.2.trans (by omega)⟩

/-- Construct the full historical post-refinement receipt.  Its balanced
cover and exact/factor-two multiplicity certificates are generated from the
exact truncation; only the positive multiplicity value is supplied explicitly. -/
noncomputable def toPostRefinementReceipt
    (receipt : PureWZ2Node05ExactMultiplicityPostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed) :
    PureWZ2Node05PostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed where
  fineRefinementExponent := receipt.fineRefinementExponent
  fineRefinement := receipt.fineRefinement
  coarseRefinementExponent := receipt.coarseRefinementExponent
  coarseRefinement := receipt.coarseRefinement
  data := receipt.data
  logExponent_eq := receipt.logExponent_eq
  selected_eq := receipt.selected_eq
  refined_eq := receipt.refined_eq
  coarse_eq := receipt.coarse_eq
  croppedCoarseShading_eq := receipt.croppedCoarseShading_eq
  balanced := receipt.data.balanced.toNode5OfExactMultiplicity
    receipt.exactMultiplicity receipt.exactMultiplicity_pos
      receipt.final_exact_multiplicity receipt.fineCellNested
  fineMultiplicity := receipt.exactMultiplicity
  fineMultiplicity_pos := receipt.exactMultiplicity_pos
  refined_multiplicity_band := receipt.final_multiplicity_band
  refined_extremal := receipt.refined_extremal
  refined_volume_lower := receipt.refined_volume_lower
  full_fiber_uniform := receipt.full_fiber_uniform
  coarse_volume_lower := receipt.coarse_volume_lower

end PureWZ2Node05ExactMultiplicityPostRefinementReceipt

/-- Pair one exact reentrant seed with the reduced exact-multiplicity receipt. -/
structure PureWZ2Node05ExactMultiplicityPostRefinementData
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (seedNormalizationExponent seedLogExponent logExponent : ℕ) where
  seed :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
  post :
    PureWZ2Node05ExactMultiplicityPostRefinementReceipt
      (outputLoss := outputLoss) (logExponent := logExponent) seed

namespace PureWZ2Node05ExactMultiplicityPostRefinementData

variable
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent logExponent : ℕ}

/-- Forget the reduced wrapper after deriving all redundant Node-5 fields. -/
noncomputable def toReentrantPostRefinementData
    (output : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    PureWZ2Node05ReentrantPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent where
  seed := output.seed
  post := output.post.toPostRefinementReceipt

/-- Directly expose the downstream Node-5 object. -/
noncomputable def toNode5StickyData
    (output : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent
        logExponent) :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent :=
  output.toReentrantPostRefinementData.toNode5StickyData

end PureWZ2Node05ExactMultiplicityPostRefinementData

end Kakeya.Assouad

end
