import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFiberwiseAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ScaleChoice
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OneScaleRescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading

/-!
# Top-level Convex-Wolff recovery from literal pure nearby-scale CWA

This module uses only the literal `WZ2PaperPureCWAAtNearbyScales` interface.
For the requested scale `delta ^ loss`, the strict nearby window with constant
`delta ^ (-loss)` forces the actual scale below one.  The actual outer-John
body CWA is pulled back to the complete ordinary strict fiber, and the
fiberwise estimates are summed through the parent relation.

The pure interface has no fixed-support hypothesis.  Consequently the final
conversion from ordinary carriers to cropped paper carriers is stated under
the exact pointwise carrier containment it needs.  `IsInUnitBall` is supplied
as a convenient corollary.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The inverse outer-John normalization has determinant at most
`4 / rho ^ 2`. -/
private theorem wz2PaperAssouadNormalization_abs_det_le
    {rho : ℝ}
    (parent : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    |LinearMap.det
        (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| ≤
      4 / rho ^ 2 := by
  let outer :=
    normalization.parent_convex_body.outerJohnEllipsoidMap
  have houterLower :
      rho ^ 2 / 4 ≤
        |LinearMap.det (outer : Point3 →ₗ[ℝ] Point3)| :=
    wz2Paper_outerJohn_abs_det_lower parent hrho
  have houterPos :
      0 < |LinearMap.det (outer : Point3 →ₗ[ℝ] Point3)| := by
    exact
      abs_pos.mpr
        (LinearEquiv.isUnit_det' outer).ne_zero
  have hscalePos : 0 < rho ^ 2 / 4 := by positivity
  have hinverse :
      |LinearMap.det (outer : Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
        (rho ^ 2 / 4)⁻¹ :=
    (inv_le_inv₀ houterPos hscalePos).2 houterLower
  have hlinear :
      (normalization.map.linear : Point3 →ₗ[ℝ] Point3) =
        (outer.symm : Point3 →ₗ[ℝ] Point3) := rfl
  rw [hlinear, LinearEquiv.det_coe_symm, abs_inv]
  calc
    |LinearMap.det (outer : Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
        (rho ^ 2 / 4)⁻¹ := hinverse
    _ = 4 / rho ^ 2 := by
      field_simp [hrho.ne']

/-- At an actual scale above `delta`, the inverse outer-John normalization
loses at most `4 * delta ^ (-2 * loss)` in volume. -/
private theorem wz2PaperAssouadNormalization_volume_image_le
    {delta loss rho : ℝ}
    (hdelta : 0 < delta)
    (hrequestedRho : Real.rpow delta loss ≤ rho)
    (parent : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData parent)
    (targetSet : Set Point3) :
    volume (normalization.map '' targetSet) ≤
      ((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss)) *
        volume targetSet := by
  rw [wz2PaperAffineEquiv_volume_image_eq]
  have hdet :
      ENNReal.ofReal
          |LinearMap.det
            (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| ≤
        (4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss) := by
    calc
      ENNReal.ofReal
          |LinearMap.det
            (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| ≤
          ENNReal.ofReal (4 / rho ^ 2) :=
        ENNReal.ofReal_mono
          (wz2PaperAssouadNormalization_abs_det_le
            parent
            ((Real.rpow_pos_of_pos hdelta loss).trans_le hrequestedRho)
            normalization)
      _ =
          (4 : ENNReal) *
            Kakeya.realRpowENN rho (-2) := by
        have hrhoPos :
            0 < rho :=
          (Real.rpow_pos_of_pos hdelta loss).trans_le hrequestedRho
        have hrpowNeg :
            Real.rpow rho (-2) = (rho ^ 2)⁻¹ := by
          simpa [Real.rpow_two] using
            Real.rpow_neg hrhoPos.le (2 : ℝ)
        rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by
          norm_num]
        rw [Kakeya.realRpowENN,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [hrpowNeg]
        field_simp [hrhoPos.ne']
      _ ≤
          (4 : ENNReal) *
            Kakeya.realRpowENN (Real.rpow delta loss) (-2) := by
        gcongr
        exact
          pure_wz2_target_negative_power_upper
            (Real.rpow_pos_of_pos hdelta loss)
            hrequestedRho (by norm_num : (0 : ℝ) ≤ 2)
      _ =
          (4 : ENNReal) *
            Kakeya.realRpowENN delta (-2 * loss) := by
        have hpower :
            Kakeya.realRpowENN (Real.rpow delta loss) (-2) =
              Kakeya.realRpowENN delta (-2 * loss) := by
          unfold Kakeya.realRpowENN
          congr 1
          calc
            Real.rpow (Real.rpow delta loss) (-2) =
                Real.rpow delta (loss * (-2)) :=
              (Real.rpow_mul hdelta.le loss (-2)).symm
            _ = Real.rpow delta (-2 * loss) := by
              congr 1
              ring
        rw [hpower]
  gcongr

/-- Pull the actual outer-John CWA on one complete strict fiber back to the
ordinary carriers of that same complete fiber. -/
theorem wz2PaperPureActualJohnFullFiber_ordinaryCWA
    {delta loss rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (hdelta : 0 < delta)
    (hrequestedRho : Real.rpow delta loss ≤ rho)
    {C : ENNReal}
    (data :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := fine) (coarse := coarse) parent C) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureFullFiberSubfamily
        fine coarse parent).family.toBodyFamily
      (((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss)) * C) := by
  let source :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fine) (coarse := coarse) parent data.normalization
  let target :=
    (wz2PaperPureFullFiberSubfamily
      fine coarse parent).family.toBodyFamily
  let coordinateChange := data.normalization.map.symm
  let indexEquiv : Fin target.card ≃ Fin source.card :=
    Equiv.refl _
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      coordinateChange indexEquiv
  · intro targetIndex point hpoint
    rcases hpoint with
      ⟨johnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    have hcancel :
        coordinateChange
            (data.normalization.map sourcePoint) =
          sourcePoint := by
      simp [coordinateChange]
    rw [hcancel]
    change
      sourcePoint ∈
        (fine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
            (indexEquiv targetIndex)).1).carrier at hsourcePoint
    have hindex : indexEquiv targetIndex = targetIndex := rfl
    rw [hindex] at hsourcePoint
    change
      sourcePoint ∈
        (fine.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv parent)
            targetIndex).1).carrier
    exact hsourcePoint
  · intro targetSet
    change
      volume (data.normalization.map '' targetSet) ≤
        ((4 : ENNReal) *
            Kakeya.realRpowENN delta (-2 * loss)) *
          volume targetSet
    exact
      wz2PaperAssouadNormalization_volume_image_le
        hdelta hrequestedRho
        (coarse.tube parent) data.normalization targetSet
  · exact data.convex_wolff

/--
Request `rho₀ = delta ^ loss` from literal pure nearby-scale CWA.

The strict scale window gives
`rho < delta ^ (-loss) * delta ^ loss = 1`; in particular the actual
partitioning scale is a genuine subunit scale even though this fact is not
stored in the type of `WZ2PaperPureNearbyScaleCoverData`.
-/
theorem wz2PaperPureNearby_topScaleWitness
    {delta loss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss))) :
    ∃ (requested : WZ2PaperRequestedScale delta)
        (nearby :
          WZ2PaperPureNearbyScaleCoverData
            family requested
            (Kakeya.realRpowENN delta (-loss))),
      nearby.rho < 1 ∧
      Real.rpow delta loss ≤ nearby.rho := by
  rcases
      pure_wz2_scale_and_nearby_generalized
        hdelta hdeltaOne hloss (le_refl loss) hlossOne
        (C := Kakeya.realRpowENN delta (-loss))
        rfl hcwa
    with
    ⟨requested, nearby, hrhoUpper, _hrhoOne,
      _hdeltaDivRho, hrequestedRho, _hrhoPos⟩
  have hrpowZero : Real.rpow delta (loss - loss) = 1 := by
    simp
  rw [hrpowZero] at hrhoUpper
  exact ⟨requested, nearby, hrhoUpper, hrequestedRho⟩

/--
Literal nearby-scale CWA at `delta ^ (-loss)` recovers ordinary-carrier
Convex-Wolff counting on the original family.

The only loss is the inverse actual outer-John Jacobian:
`4 * delta ^ (-2 * loss)`.  Summing complete strict fibers introduces no
additional factor.
-/
theorem wz2PaperPureNearby_topLevelOrdinaryCWA
    {delta loss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss))) :
    WZ2PaperBodyConvexWolffBound
      family.toBodyFamily
      (((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss)) *
        Kakeya.realRpowENN delta (-loss)) := by
  rcases
      wz2PaperPureNearby_topScaleWitness
        hdelta hdeltaOne hloss hlossOne hcwa
    with
    ⟨_requested, nearby, _hrhoOne, hrequestedRho⟩
  let scaleData := nearby.scaleData
  let coarse := scaleData.coarse
  let cover := scaleData.cover
  by_cases hfamilyCard : family.card = 0
  · intro convexSet _hconvex
    unfold Kakeya.Streamlined.BodyFamily.containedCount
    have hcardZero :
        (family.toBodyFamily.containedIndices convexSet).card = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpositive
      rcases Finset.card_pos.mp hpositive with ⟨index, _hindex⟩
      exact Fin.elim0 (hfamilyCard ▸ index)
    rw [hcardZero]
    simp
  · have hparentCount : 0 < coarse.card := by
      let source : Fin family.card :=
        ⟨0, Nat.pos_of_ne_zero hfamilyCard⟩
      rcases cover.covers source with ⟨parent, _hparent⟩
      exact Nat.zero_lt_of_lt parent.isLt
    apply
      wz2PaperBodyConvexWolffBound_of_parent_fibers
        hparentCount cover.parent
    intro parent
    rcases scaleData.rescaledFiber parent with ⟨fiberData⟩
    have hfullFiber :
        WZ2PaperBodyConvexWolffBound
          (wz2PaperPureFullFiberSubfamily
            family coarse parent).family.toBodyFamily
          (((4 : ENNReal) *
              Kakeya.realRpowENN delta (-2 * loss)) *
            Kakeya.realRpowENN delta (-loss)) :=
      wz2PaperPureActualJohnFullFiber_ordinaryCWA
        parent hdelta hrequestedRho fiberData
    have hindices :
        wz2PaperOrdinaryFullFiberIndices family coarse parent =
          Finset.univ.filter fun source =>
            cover.parent source = parent := by
      ext source
      simp only [
        Finset.mem_filter,
        Finset.mem_univ,
        true_and
      ]
      exact
        cover.mem_fullFiber_iff_parent_eq
          scaleData.rho_pos.le parent source
    simp only [
      wz2PaperPureFullFiberSubfamily,
      Kakeya.Streamlined.TubeSubfamily.fromFinset,
      Kakeya.Streamlined.TubeFamily.toBodyFamily
    ] at hfullFiber
    rw [hindices] at hfullFiber
    unfold wz2PaperBodyParentFiber
    convert hfullFiber using 1
    simp only [Kakeya.Streamlined.TubeFamily.toBodyFamily]
    rfl

/--
The exact container condition needed to pass from ordinary tube carriers to
the cropped paper carriers on the same indexed family.
-/
theorem wz2PaperOrdinaryCWA_to_paper_of_carrier_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (carrierSubset :
      ∀ index,
        (family.tube index).carrier ⊆
          wz1PaperTubeCarrier (family.tube index))
    (ordinary :
      WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    WZ2PaperConvexWolffBound family C := by
  intro convexSet hconvex
  have hindices :
      (Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet) ⊆
      (Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet) := by
    intro index hindex
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index,
        (carrierSubset index).trans
          (Finset.mem_filter.mp hindex).2⟩
  have hcount :
      (wz1PaperBodyFamily family).containedCount convexSet ≤
        family.toBodyFamily.containedCount convexSet := by
    change
      ((Finset.univ.filter fun index : Fin family.card =>
        wz1PaperTubeCarrier (family.tube index) ⊆ convexSet).card :
          ENNReal) ≤
      ((Finset.univ.filter fun index : Fin family.card =>
        (family.tube index).carrier ⊆ convexSet).card : ENNReal)
    exact_mod_cast Finset.card_le_card hindices
  exact hcount.trans (ordinary convexSet hconvex)

/--
The top-level paper CWA under the thinnest required geometric container
condition, before absorbing the fixed dimensional and Jacobian losses.
-/
theorem wz2PaperPureNearby_topLevelPaperCWA
    {delta loss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss)))
    (carrierSubset :
      ∀ index,
        (family.tube index).carrier ⊆
          wz1PaperTubeCarrier (family.tube index)) :
    WZ2PaperConvexWolffBound
      family
      (((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss)) *
        Kakeya.realRpowENN delta (-loss)) :=
  wz2PaperOrdinaryCWA_to_paper_of_carrier_subset
    carrierSubset
    (wz2PaperPureNearby_topLevelOrdinaryCWA
      hdelta hdeltaOne hloss hlossOne hcwa)

/-- Absorb the complete actual-John pullback loss into the output exponent. -/
private theorem wz2PaperPureNearby_pullbackLoss_le
    {delta loss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (habsorb :
      (4 : ENNReal) *
          Kakeya.realRpowENN delta (outputLoss - 3 * loss) ≤
        1) :
    ((4 : ENNReal) *
          Kakeya.realRpowENN delta (-2 * loss)) *
        Kakeya.realRpowENN delta (-loss) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
  have hleft :
      ((4 : ENNReal) *
            Kakeya.realRpowENN delta (-2 * loss)) *
          Kakeya.realRpowENN delta (-loss) =
        (4 : ENNReal) *
          Kakeya.realRpowENN delta (-3 * loss) := by
    rw [mul_assoc, Subunit.realRpowENN_mul hdelta]
    congr 2
    ring
  have hfactor :
      (4 : ENNReal) *
          Kakeya.realRpowENN delta (-3 * loss) =
        ((4 : ENNReal) *
            Kakeya.realRpowENN delta (outputLoss - 3 * loss)) *
          Kakeya.realRpowENN delta (-outputLoss) := by
    calc
      (4 : ENNReal) *
          Kakeya.realRpowENN delta (-3 * loss) =
        (4 : ENNReal) *
          Kakeya.realRpowENN delta
            ((outputLoss - 3 * loss) + (-outputLoss)) := by
              congr 2
              ring
      _ =
        (4 : ENNReal) *
          (Kakeya.realRpowENN delta (outputLoss - 3 * loss) *
            Kakeya.realRpowENN delta (-outputLoss)) := by
              rw [Subunit.realRpowENN_mul hdelta]
      _ =
        ((4 : ENNReal) *
            Kakeya.realRpowENN delta (outputLoss - 3 * loss)) *
          Kakeya.realRpowENN delta (-outputLoss) := by
              ring
  rw [hleft, hfactor]
  calc
    ((4 : ENNReal) *
          Kakeya.realRpowENN delta (outputLoss - 3 * loss)) *
        Kakeya.realRpowENN delta (-outputLoss) ≤
      1 * Kakeya.realRpowENN delta (-outputLoss) := by
        gcongr
    _ = Kakeya.realRpowENN delta (-outputLoss) := one_mul _

/--
Fixed-scale recovery of the requested paper CWA after an explicit output-loss
absorption.
-/
theorem wz2PaperPureNearby_topLevelPaperCWA_of_outputLoss
    {delta loss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales
        family (Kakeya.realRpowENN delta (-loss)))
    (carrierSubset :
      ∀ index,
        (family.tube index).carrier ⊆
          wz1PaperTubeCarrier (family.tube index))
    (habsorb :
      (4 : ENNReal) *
          Kakeya.realRpowENN delta (outputLoss - 3 * loss) ≤
        1) :
    WZ2PaperConvexWolffBound
      family
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  have hpaper :=
    wz2PaperPureNearby_topLevelPaperCWA
      hdelta hdeltaOne hloss hlossOne hcwa carrierSubset
  have hconstant :
      ((4 : ENNReal) *
            Kakeya.realRpowENN delta (-2 * loss)) *
          Kakeya.realRpowENN delta (-loss) ≤
        Kakeya.realRpowENN delta (-outputLoss) :=
    wz2PaperPureNearby_pullbackLoss_le hdelta habsorb
  intro convexSet hconvex
  exact
    (hpaper convexSet hconvex).trans <| by
      gcongr

/--
Uniform small-scale top-level recovery.  A positive gap
`outputLoss - 3 * loss` absorbs the fixed dimensional constant and the two
inverse powers contributed by the actual outer-John pullback.
-/
theorem wz2PaperPureNearby_topLevelPaperCWA_eventually
    {loss outputLoss : ℝ}
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    (hgap : 3 * loss < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          WZ2PaperPureCWAAtNearbyScales
              family (Kakeya.realRpowENN delta (-loss)) →
            (∀ index,
              (family.tube index).carrier ⊆
                wz1PaperTubeCarrier (family.tube index)) →
              WZ2PaperConvexWolffBound
                family
                (Kakeya.realRpowENN delta (-outputLoss)) := by
  rcases
      pure_wz2_exists_delta₀_constant_rpow_le_one
        (constant := 4)
        (gap := outputLoss - 3 * loss)
        (by norm_num)
        (by linarith)
    with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall family hcwa carrierSubset
  exact
    wz2PaperPureNearby_topLevelPaperCWA_of_outputLoss
      hdelta (hdeltaSmall.trans hdelta₀One)
      hloss hlossOne hcwa carrierSubset
      (by simpa using habsorb delta hdelta hdeltaSmall)

/-- The fixed-support convention supplies the required paper carrier
containment. -/
theorem wz2PaperPureNearby_topLevelPaperCWA_eventually_of_isInUnitBall
    {loss outputLoss : ℝ}
    (hloss : 0 < loss)
    (hlossOne : loss ≤ 1)
    (hgap : 3 * loss < outputLoss) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.IsInUnitBall →
            WZ2PaperPureCWAAtNearbyScales
                family (Kakeya.realRpowENN delta (-loss)) →
              WZ2PaperConvexWolffBound
                family
                (Kakeya.realRpowENN delta (-outputLoss)) := by
  rcases
      wz2PaperPureNearby_topLevelPaperCWA_eventually
        hloss hlossOne hgap
    with
    ⟨delta₀, hdelta₀, hdelta₀One, recover⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall family hsupport hcwa
  apply
    recover delta hdelta hdeltaSmall family hcwa
  intro index
  exact
    wz2_paper_ordinary_carrier_subset_cropped
      hdelta.le (family.tube index) (hsupport index)

end Kakeya.Assouad

end
