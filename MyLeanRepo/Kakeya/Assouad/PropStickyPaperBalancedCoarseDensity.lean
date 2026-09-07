import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Coarse density from a balanced fine shading

For a balanced cover, a common fine-fiber multiplicity cap gives

`fine mass ≤ fiberCap * coarse shaded mass`.

Combining this with a retained fine-mass lower bound and the universal
quadratic mass upper bound for the full coarse tubes proves aggregate density
of the coarse shading.  This is the paper's mass transfer immediately after
the definition of `tilde Y`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_balanced_coarse_density
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 24)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (balanced :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover fineShading coarseShading)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (fiberCap massLower lambda : ENNReal)
    (hFiberZero : fiberCap ≠ 0)
    (hFiberTop : fiberCap ≠ ⊤)
    (hFiberMultiplicity :
      ∀ parent point,
        (cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          fiberCap)
    (hMassLower : massLower ≤ fineShading.mass)
    (hAbsorb :
      lambda *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN rho 2) *
            coarse.enncard *
            fiberCap ≤
        massLower) :
    coarseShading.IsLambdaDense lambda := by
  have hFineToCoarse :
      fineShading.mass ≤ fiberCap * coarseShading.mass :=
    cover.toWZ1PaperTubeCover.fine_mass_le_fiberCap_mul_coarse_mass
      fineShading coarseShading balanced.point_compatibility
      hFiberMultiplicity
  have hCoarseMassLower :
      massLower ≤ fiberCap * coarseShading.mass :=
    hMassLower.trans hFineToCoarse
  let fullShading : WZ1PaperTubeShading coarse :=
    { carrier := fun index =>
        wz1PaperTubeCarrier (coarse.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable (coarse.tube index)
      subset_body := fun _ => Set.Subset.rfl }
  have hBodyMass :
      (wz1PaperBodyFamily coarse).mass ≤
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2) *
          coarse.enncard := by
    have h :=
      wz2_paper_shading_mass_upper
        hrho hrhoSmall coarseLine fullShading
    change
      (wz1PaperBodyFamily coarse).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho 2 * coarse.enncard at h
    simpa [mul_assoc] using h
  have hScaled :
      fiberCap *
          (lambda * (wz1PaperBodyFamily coarse).mass) ≤
        fiberCap * coarseShading.mass := by
    calc
      fiberCap *
            (lambda * (wz1PaperBodyFamily coarse).mass) ≤
          fiberCap *
            (lambda *
              (((55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN rho 2) *
                coarse.enncard)) := by
        gcongr
      _ =
          lambda *
              ((55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN rho 2) *
              coarse.enncard * fiberCap := by
        ring
      _ ≤ massLower := hAbsorb
      _ ≤ fiberCap * coarseShading.mass := hCoarseMassLower
  have hScaledRight :
      (lambda * (wz1PaperBodyFamily coarse).mass) * fiberCap ≤
        coarseShading.mass * fiberCap := by
    simpa [mul_comm] using hScaled
  exact
    (ENNReal.mul_le_mul_iff_left hFiberZero hFiberTop).mp hScaledRight

end Kakeya.Assouad

end
