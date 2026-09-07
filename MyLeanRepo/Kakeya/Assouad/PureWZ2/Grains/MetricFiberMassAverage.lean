import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BalancedFiniteRebalancedCoarsePlaneMap
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization

/-!
# Average retained mass in one metric fibre

The complete fibres of one frozen Section 6 cover partition both the source
and refined shaded masses.  Hence a global `1 / K` retention forces the same
relative retention in at least one complete metric fibre.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open ENNReal

/-- The literal complete-fibre shading used by the frozen Node 3 rescaling
output has mass equal to the corresponding fibre shaded mass. -/
lemma completeFiberShading_mass_eq_fiberShadedMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (wz2PaperFullFiberIndices fine coarse parent)) shading).mass =
      cover.toPaperTubeCover.fiberShadedMass shading parent := by
  rw [restrictPaperShading_fromFinset_mass]
  simp only [WZ1PaperTubeCover.fiberShadedMass]
  congr 1
  exact cover.fullFiberIndices_eq parent

/-- Select a complete parent fibre whose shaded mass per tube is at least the
ambient average.  This is the fibre selection needed in Proposition 6.3:
unlike selecting a largest fibre by absolute mass, it introduces no factor
equal to the number of coarse parents. -/
theorem exists_metric_fiber_density_average
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hcoarseNonempty : coarse.Nonempty)
    (density scaleMass : ENNReal)
    (hglobal : density * fine.enncard * scaleMass ≤ shading.mass) :
    ∃ parent : Fin coarse.card,
      density *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
          scaleMass ≤
        cover.toPaperTubeCover.fiberShadedMass shading parent := by
  have hcardinality :
      (∑ parent : Fin coarse.card,
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) =
        fine.enncard := by
    have hpartition :
        ∑ parent : Fin coarse.card,
            (cover.toPaperTubeCover.fiberIndices parent).card =
          fine.card := by
      have hraw := (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin fine.card)))
        (t := (Finset.univ : Finset (Fin coarse.card)))
        (f := cover.toPaperTubeCover.parent)
        (fun _ _ => Finset.mem_univ _)).symm
      simpa only [WZ1PaperTubeCover.fiberIndices, Finset.card_univ,
        Fintype.card_fin] using hraw
    have hpartitionENN :
        (∑ parent : Fin coarse.card,
            ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal)) =
          (fine.card : ENNReal) := by
      exact_mod_cast hpartition
    calc
      (∑ parent : Fin coarse.card,
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) =
          ∑ parent : Fin coarse.card,
            ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [cover.fullFiberIndices_eq]
      _ = (fine.card : ENNReal) := hpartitionENN
      _ = fine.enncard := rfl
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  letI : Nonempty (Fin coarse.card) := ⟨⟨0, hcoarseNonempty⟩⟩
  have hstrict :
      (∑ parent : Fin coarse.card,
          cover.toPaperTubeCover.fiberShadedMass shading parent) <
        ∑ parent : Fin coarse.card,
          density *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
            scaleMass :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun parent _ => hnone parent)
  have hright :
      (∑ parent : Fin coarse.card,
          density *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
            scaleMass) =
        density * fine.enncard * scaleMass := by
    calc
      (∑ parent : Fin coarse.card,
          density *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
            scaleMass) =
          (∑ parent : Fin coarse.card,
            density *
              ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) *
            scaleMass := by rw [Finset.sum_mul]
      _ = density *
            (∑ parent : Fin coarse.card,
              ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) *
            scaleMass := by rw [Finset.mul_sum]
      _ = density * fine.enncard * scaleMass := by rw [hcardinality]
  rw [cover.sum_fiberShadedMass shading, hright] at hstrict
  exact (not_lt_of_ge hglobal) hstrict

/-- Select one complete parent fibre which is simultaneously mass-maximal and
has the ambient average density after paying exactly the number of coarse
parents.  This is the selection used in Proposition 6.3: the first conclusion
is the global mass-retention input for hereditary top-level CWA, while the
second is the per-tube density input for the common-slice argument. -/
theorem exists_metric_fiber_density_and_retained_average
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hcoarseNonempty : coarse.Nonempty)
    (density scaleMass : ENNReal)
    (hglobal : density * fine.enncard * scaleMass ≤ shading.mass) :
    ∃ parent : Fin coarse.card,
      shading.mass ≤
          coarse.enncard *
            cover.toPaperTubeCover.fiberShadedMass shading parent ∧
      (coarse.enncard⁻¹ * density) *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
          scaleMass ≤
        cover.toPaperTubeCover.fiberShadedMass shading parent := by
  let fiberMass : Fin coarse.card → ENNReal := fun parent =>
    cover.toPaperTubeCover.fiberShadedMass shading parent
  let reference : Fin coarse.card := ⟨0, hcoarseNonempty⟩
  have hparents : (Finset.univ : Finset (Fin coarse.card)).Nonempty :=
    ⟨reference, Finset.mem_univ _⟩
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin coarse.card)) fiberMass hparents with
    ⟨parent, _, hmax⟩
  have hsum : shading.mass =
      ∑ candidate : Fin coarse.card, fiberMass candidate := by
    exact (cover.sum_fiberShadedMass shading).symm
  have hretained : shading.mass ≤ coarse.enncard * fiberMass parent := by
    rw [hsum]
    calc
      (∑ candidate : Fin coarse.card, fiberMass candidate) ≤
          ∑ _candidate : Fin coarse.card, fiberMass parent := by
        exact Finset.sum_le_sum fun candidate _ =>
          hmax candidate (Finset.mem_univ _)
      _ = coarse.enncard * fiberMass parent := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
  have hcoarseZero : coarse.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      hcoarseNonempty.ne'
  have hcoarseTop : coarse.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hfiberCard :
      ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) ≤
        fine.enncard := by
    change
      ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) ≤
        (fine.card : ENNReal)
    exact_mod_cast (show
      (wz2PaperFullFiberIndices fine coarse parent).card ≤ fine.card by
        simpa only [Fintype.card_fin] using
          (Finset.card_le_univ
            (s := wz2PaperFullFiberIndices fine coarse parent)))
  have hdensity :
      (coarse.enncard⁻¹ * density) *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
          scaleMass ≤ fiberMass parent := by
    calc
      (coarse.enncard⁻¹ * density) *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
            scaleMass =
          coarse.enncard⁻¹ *
            (density *
              ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
              scaleMass) := by ring
      _ ≤ coarse.enncard⁻¹ *
          (density * fine.enncard * scaleMass) := by
        gcongr
      _ ≤ coarse.enncard⁻¹ * shading.mass := by gcongr
      _ ≤ coarse.enncard⁻¹ *
          (coarse.enncard * fiberMass parent) := by gcongr
      _ = fiberMass parent := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcoarseZero hcoarseTop,
          one_mul]
  exact ⟨parent, hretained, hdensity⟩

/-- Select one complete parent fibre whose refined shaded mass retains the
global relative fraction. -/
theorem exists_metric_fiber_retained_mass_average
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (source refined : WZ1PaperTubeShading fine)
    (hcoarseNonempty : coarse.Nonempty)
    (K : ENNReal)
    (hKPos : 0 < K)
    (hKFinite : K ≠ ⊤)
    (hmass : K⁻¹ * source.mass ≤ refined.mass) :
    ∃ parent : Fin coarse.card,
      K⁻¹ * cover.toPaperTubeCover.fiberShadedMass source parent ≤
        cover.toPaperTubeCover.fiberShadedMass refined parent := by
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hstrict :
      (∑ parent : Fin coarse.card,
          cover.toPaperTubeCover.fiberShadedMass refined parent) <
        ∑ parent : Fin coarse.card,
          K⁻¹ * cover.toPaperTubeCover.fiberShadedMass source parent := by
    letI : Nonempty (Fin coarse.card) := ⟨⟨0, hcoarseNonempty⟩⟩
    exact ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun parent _ => hnone parent)
  have hright :
      (∑ parent : Fin coarse.card,
          K⁻¹ * cover.toPaperTubeCover.fiberShadedMass source parent) =
        K⁻¹ * source.mass := by
    rw [← Finset.mul_sum, cover.sum_fiberShadedMass source]
  have hleft :
      (∑ parent : Fin coarse.card,
          cover.toPaperTubeCover.fiberShadedMass refined parent) =
        refined.mass := cover.sum_fiberShadedMass refined
  rw [hleft, hright] at hstrict
  exact (not_lt_of_ge hmass) hstrict

/-- Normalize the exact-rebalancing mass account and select one parent whose
complete metric fibre retains the same relative fraction. -/
theorem BalancedFiniteRebalancedCoarsePlaneMapData.exists_retained_metric_fiber
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (data : BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta)
    (hcoarseNonempty : coarse.Nonempty) :
    let K : ENNReal := 1 + finite.leftFactor⁻¹ *
      (finite.rightFactor * rebalancedFiniteExactLoss data.rebalanced)
    ∃ parent : Fin coarse.card,
      K⁻¹ * cover.toPaperTubeCover.fiberShadedMass fineShading parent ≤
        cover.toPaperTubeCover.fiberShadedMass
          data.rebalanced.balancing.refined parent := by
  let rawLoss : ENNReal := finite.leftFactor⁻¹ *
    (finite.rightFactor * rebalancedFiniteExactLoss data.rebalanced)
  let K : ENNReal := 1 + rawLoss
  have hKPos : 0 < K := zero_lt_one.trans_le (le_add_right le_rfl)
  have hexactFinite : rebalancedFiniteExactLoss data.rebalanced ≠ ⊤ := by
    have hbandFinite : rebalancedFiniteBandLoss fine.card ≠ ⊤ := by
      simp [rebalancedFiniteBandLoss]
    have hlogFinite :
        ((4 : ENNReal) *
          ((Nat.log 2
            (∑ coarseCell ∈ data.rebalanced.pruning.coarseCells,
              (data.rebalanced.pruning.availableFineCells coarseCell).card) +
              1 : ℕ) : ENNReal)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) (by simp)
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hbandFinite (by norm_num)) hlogFinite
  have hrawFinite : rawLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr finite.leftFactor_pos.ne')
      (ENNReal.mul_ne_top finite.rightFactor_ne_top hexactFinite)
  have hKFinite : K ≠ ⊤ := by
    rw [show K = 1 + rawLoss by rfl, ENNReal.add_ne_top]
    exact ⟨by norm_num, hrawFinite⟩
  have hsourceRefined : fineShading.mass ≤
      rawLoss * data.rebalanced.balancing.refined.mass := by
    calc
      fineShading.mass = finite.leftFactor⁻¹ *
          (finite.leftFactor * fineShading.mass) := by
        rw [ENNReal.inv_mul_cancel_left finite.leftFactor_pos.ne'
          finite.leftFactor_ne_top]
      _ ≤ finite.leftFactor⁻¹ *
          ((finite.rightFactor *
              rebalancedFiniteExactLoss data.rebalanced) *
            data.rebalanced.balancing.refined.mass) := by
        exact mul_le_mul_left' data.fine_mass_retention _
      _ = rawLoss * data.rebalanced.balancing.refined.mass := by
        simp only [rawLoss]
        ring
  have hmass : K⁻¹ * fineShading.mass ≤
      data.rebalanced.balancing.refined.mass := by
    apply (ENNReal.inv_mul_le_iff hKPos.ne' hKFinite).2
    calc
      fineShading.mass ≤
          rawLoss * data.rebalanced.balancing.refined.mass :=
        hsourceRefined
      _ ≤ K * data.rebalanced.balancing.refined.mass := by
        gcongr
        exact le_add_left le_rfl
  simpa only [K, rawLoss] using
    exists_metric_fiber_retained_mass_average cover fineShading
      data.rebalanced.balancing.refined hcoarseNonempty K hKPos
      hKFinite hmass

/-- The exact-rebalancing account bounds the original shaded mass by the
one-sided finite loss times the rebalanced shaded mass. -/
theorem BalancedFiniteRebalancedCoarsePlaneMapData.source_mass_le_rebalanced_mass
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (data : BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta) :
    fineShading.mass ≤
      (1 + finite.leftFactor⁻¹ *
          (finite.rightFactor *
            rebalancedFiniteExactLoss data.rebalanced)) *
        data.rebalanced.balancing.refined.mass := by
  let rawLoss : ENNReal := finite.leftFactor⁻¹ *
    (finite.rightFactor * rebalancedFiniteExactLoss data.rebalanced)
  calc
    fineShading.mass = finite.leftFactor⁻¹ *
        (finite.leftFactor * fineShading.mass) := by
      rw [ENNReal.inv_mul_cancel_left finite.leftFactor_pos.ne'
        finite.leftFactor_ne_top]
    _ ≤ finite.leftFactor⁻¹ *
        ((finite.rightFactor *
            rebalancedFiniteExactLoss data.rebalanced) *
          data.rebalanced.balancing.refined.mass) := by
      exact mul_le_mul_left' data.fine_mass_retention _
    _ = rawLoss * data.rebalanced.balancing.refined.mass := by
      simp only [rawLoss]
      ring
    _ ≤ (1 + rawLoss) *
        data.rebalanced.balancing.refined.mass := by
      gcongr
      exact le_add_left le_rfl

/-- Select a complete metric fibre whose *rebalanced* shaded mass is at
least the average over all parents.  Combined with the exact-rebalancing
account, this gives an absolute source-to-fibre loss, rather than merely a
relative comparison between the source and refined shadings inside a fibre.
This is the form needed to retain the ambient family's top-level CWA. -/
theorem BalancedFiniteRebalancedCoarsePlaneMapData.exists_global_retained_metric_fiber_shading
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (data : BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta)
    (hcoarseNonempty : coarse.Nonempty) :
    ∃ parent : Fin coarse.card,
      fineShading.mass ≤
        ((1 + finite.leftFactor⁻¹ *
            (finite.rightFactor *
              rebalancedFiniteExactLoss data.rebalanced)) *
          coarse.enncard) *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          data.rebalanced.balancing.refined).mass := by
  let fiberMass : Fin coarse.card → ENNReal := fun parent =>
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (wz2PaperFullFiberIndices fine coarse parent))
      data.rebalanced.balancing.refined).mass
  let reference : Fin coarse.card := ⟨0, hcoarseNonempty⟩
  have hparents : (Finset.univ : Finset (Fin coarse.card)).Nonempty :=
    ⟨reference, Finset.mem_univ _⟩
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin coarse.card)) fiberMass hparents with
    ⟨parent, _, hmax⟩
  refine ⟨parent, ?_⟩
  have hsum : data.rebalanced.balancing.refined.mass =
      ∑ candidate : Fin coarse.card, fiberMass candidate := by
    rw [← cover.sum_fiberShadedMass]
    apply Finset.sum_congr rfl
    intro candidate _
    exact (completeFiberShading_mass_eq_fiberShadedMass
      cover data.rebalanced.balancing.refined candidate).symm
  have haverage : data.rebalanced.balancing.refined.mass ≤
      coarse.enncard * fiberMass parent := by
    rw [hsum]
    calc
      (∑ candidate : Fin coarse.card, fiberMass candidate) ≤
          ∑ _candidate : Fin coarse.card, fiberMass parent := by
        exact Finset.sum_le_sum fun candidate _ =>
          hmax candidate (Finset.mem_univ _)
      _ = coarse.enncard * fiberMass parent := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
  calc
    fineShading.mass ≤
        (1 + finite.leftFactor⁻¹ *
            (finite.rightFactor *
              rebalancedFiniteExactLoss data.rebalanced)) *
          data.rebalanced.balancing.refined.mass :=
      data.source_mass_le_rebalanced_mass
    _ ≤
        (1 + finite.leftFactor⁻¹ *
            (finite.rightFactor *
              rebalancedFiniteExactLoss data.rebalanced)) *
          (coarse.enncard * fiberMass parent) := by
      gcongr
    _ =
        ((1 + finite.leftFactor⁻¹ *
            (finite.rightFactor *
              rebalancedFiniteExactLoss data.rebalanced)) *
          coarse.enncard) * fiberMass parent := by
      ring


/-- Restricted-shading form of the retained metric-fibre conclusion. -/
theorem BalancedFiniteRebalancedCoarsePlaneMapData.exists_retained_metric_fiber_shading
    {delta rho target coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {finite : BalancedFinitePlaninessData
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (data : BalancedFiniteRebalancedCoarsePlaneMapData
      (target := target) original finite hdelta)
    (hcoarseNonempty : coarse.Nonempty) :
    let K : ENNReal := 1 + finite.leftFactor⁻¹ *
      (finite.rightFactor * rebalancedFiniteExactLoss data.rebalanced)
    ∃ parent : Fin coarse.card,
      K⁻¹ *
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
              (wz2PaperFullFiberIndices fine coarse parent))
            fineShading).mass ≤
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          data.rebalanced.balancing.refined).mass := by
  rcases data.exists_retained_metric_fiber hcoarseNonempty with
    ⟨parent, hparent⟩
  refine ⟨parent, ?_⟩
  rw [completeFiberShading_mass_eq_fiberShadedMass,
    completeFiberShading_mass_eq_fiberShadedMass]
  exact hparent

end Kakeya.Assouad.PureWZ2

end
