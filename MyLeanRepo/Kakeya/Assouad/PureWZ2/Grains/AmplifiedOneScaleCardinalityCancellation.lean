import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedOneScaleVariation

/-!
# Cardinality cancellation for amplified one-scale variation

The full-fiber weighted selector produces the same square of the ambient fine
cardinality that occurs in a pointwise multiplicity lower bound.  For a
nonempty fine family these factors cancel in `ENNReal`, leaving only the
scale-dependent density, fiber, and orientation powers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_amplified_one_scale_nearby_variation_cancel_cardinality
    {delta rho kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading S : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hfineNonempty : fine.Nonempty)
    (hcoarseNonempty : coarse.Nonempty)
    (hSSubFine : PaperIsSubshading S fineShading)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ p ∈ S.union,
      fineMultiplicity ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      2 * paperCloseDirectionCount S p i kappa ≤ fineMultiplicity)
    (fiberPower densityPower : ENNReal)
    (hfiber : ∀ parent p,
      (((Finset.univ.filter fun i : Fin fine.card =>
        PureWZ2.selectParent cover i = parent ∧ p ∈ S.carrier i).card : ℕ) :
        ENNReal) ≤ fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal))
    (hdensity : densityPower * fine.enncard ≤
      (fineMultiplicity : ENNReal))
    (hincidenceNonneg : 0 ≤ incidence)
    (hrho : 0 < rho) (hkappa : rho < kappa)
    (K : ℕ) (hK : 0 < K) (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ rho →
          dist (planeMap.planeMap p) (planeMap.planeMap q) ≤ rho) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      densityPower ^ 2 * S.mass ≤
        27 * ((2 * fiberPower ^ 2) *
          (wz1OrientationCapCount
            (10 * (incidence + rho / 2) / (kappa - rho)) rho : ENNReal)) *
          selected.mass := by
  rcases paper_amplified_one_scale_nearby_variation
      balanced hcoarseNonempty hSSubFine hSCubical planeMap hplaneCell
      fineMultiplicity hFineMultiplicity hclose fiberPower hfiber
      hincidenceNonneg hrho hkappa K hK hrhoAligned with
    ⟨selected, hselectedSub, hselectedCubical, hvariation,
      hselectedMultiplicity, hmass⟩
  refine ⟨selected, hselectedSub, hselectedCubical, hvariation,
    hselectedMultiplicity, ?_⟩
  let orientation : ENNReal :=
    (wz1OrientationCapCount
      (10 * (incidence + rho / 2) / (kappa - rho)) rho : ENNReal)
  have hdensitySq :
      densityPower ^ 2 * fine.enncard ^ 2 ≤
        (fineMultiplicity : ENNReal) ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left' hdensity 2
  have hscaled :
      fine.enncard ^ 2 * (densityPower ^ 2 * S.mass) ≤
        fine.enncard ^ 2 *
          (27 * ((2 * fiberPower ^ 2) * orientation) * selected.mass) := by
    calc
      fine.enncard ^ 2 * (densityPower ^ 2 * S.mass) =
          (densityPower ^ 2 * fine.enncard ^ 2) * S.mass := by ring
      _ ≤ (fineMultiplicity : ENNReal) ^ 2 * S.mass := by gcongr
      _ ≤ 27 * ((2 * fiberPower ^ 2) * fine.enncard ^ 2 * orientation) *
          selected.mass := hmass
      _ = fine.enncard ^ 2 *
          (27 * ((2 * fiberPower ^ 2) * orientation) * selected.mass) := by
        ring
  have hcardZero : fine.enncard ^ 2 ≠ 0 := by
    apply pow_ne_zero
    change (fine.card : ENNReal) ≠ 0
    have hcardNat : fine.card ≠ 0 := Nat.one_le_iff_ne_zero.mp hfineNonempty
    exact_mod_cast hcardNat
  have hcardTop : fine.enncard ^ 2 ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcancel :=
    (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp hscaled
  simpa [orientation] using hcancel

end Kakeya.Assouad

end
