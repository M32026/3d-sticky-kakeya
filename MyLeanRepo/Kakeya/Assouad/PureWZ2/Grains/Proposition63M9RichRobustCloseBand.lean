import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustCloseBand
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTransversality

/-! # Rich terminal robust close count on the prepared dyadic band -/

noncomputable section
namespace Kakeya.Assouad.PureWZ2
open Set

lemma Proposition63PaperLemma43Preparation.band_common_source
    {delta sigma sourceLoss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source) :
    ∀ index, prepared.band.band.carrier index =
      source.carrier index ∩ prepared.band.band.union := by
  intro index
  have hbandSubHigh : PaperIsSubshading
      prepared.band.band prepared.high := by
    rw [prepared.band.band_eq]
    exact wz1PaperDyadicBandSubshading_isSubshading
      prepared.high prepared.band.level
  ext point
  constructor
  · intro hpoint
    have hhigh : point ∈ prepared.high.carrier index :=
      hbandSubHigh index hpoint
    have hbandUnion : point ∈ prepared.band.band.union := ⟨index, hpoint⟩
    have hhighUnion : point ∈ prepared.high.union := ⟨index, hhigh⟩
    have hsource : point ∈ source.carrier index := by
      rw [prepared.high_common index] at hhigh
      exact hhigh.1
    exact ⟨hsource, hbandUnion⟩
  · rintro ⟨hsource, hbandUnion⟩
    have hhighUnion : point ∈ prepared.high.union := by
      rcases hbandUnion with ⟨other, hother⟩
      exact ⟨other, hbandSubHigh other hother⟩
    have hhigh : point ∈ prepared.high.carrier index := by
      rw [prepared.high_common index]
      exact ⟨hsource, hhighUnion⟩
    rcases hbandUnion with ⟨other, hother⟩
    rw [prepared.band.band_eq] at hother ⊢
    exact ⟨hhigh, hother.2⟩

theorem Proposition63RichTerminalStickyData.prepared_band_close_lt_div_twentyFour
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := outputLoss)
      (densityLoss := densityLoss) rich.data.refined)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal))
    (hm24 : 24 ≤ 2 ^ prepared.band.level) :
    ∀ point ∈ prepared.band.band.union, ∀ index,
      point ∈ prepared.band.band.carrier index →
        paperCloseDirectionCount prepared.band.band point index rho.1 <
          (2 ^ prepared.band.level) / 24 := by
  have hbandSubHigh : PaperIsSubshading prepared.band.band prepared.high := by
    rw [prepared.band.band_eq]
    exact wz1PaperDyadicBandSubshading_isSubshading
      prepared.high prepared.band.level
  have hbandSubSource :
      PaperIsSubshading prepared.band.band rich.data.refined := fun index =>
    (hbandSubHigh index).trans (prepared.high_subshading index)
  apply paper_closeDirectionCount_lt_dyadic_div_twentyFour_of_robust_floor
      (source := rich.data.refined)
      (floor := rich.terminal.fineDegreeFloor)
      (D := stickyCoarseCloseCount)
      (mu := rich.terminal.muFine)
      prepared.band_common_source hbandSubSource
      (fun point hpoint =>
        rich.terminal.fine_pointMultiplicity_floor_on_union hpoint)
      (fun point hpoint index hindex => by
        exact rich.terminal.robust_close_count
          (lt_of_lt_of_le rich.terminal.delta_pos rho.2.1)
          hrhoSmall point hpoint index hindex)
      (fun point hpoint => by
        have hlowerENN :=
          (prepared.band.band_multiplicity point hpoint).1
        rw [show (2 : ENNReal) ^ prepared.band.level =
          ((2 ^ prepared.band.level : ℕ) : ENNReal) by norm_num] at hlowerENN
        exact (Nat.cast_le :
          (((2 ^ prepared.band.level : ℕ) : ENNReal) ≤
            ((prepared.band.band.pointMultiplicity point : ℕ) : ENNReal) ↔
              2 ^ prepared.band.level ≤
                prepared.band.band.pointMultiplicity point)).mp hlowerENN)
      (fun point hpoint => by
        have hupperENN :=
          (prepared.band.band_multiplicity point hpoint).2
        rw [show (2 : ENNReal) ^ (prepared.band.level + 1) =
          ((2 ^ (prepared.band.level + 1) : ℕ) : ENNReal) by norm_num] at hupperENN
        have hupperNat : prepared.band.band.pointMultiplicity point <
            2 ^ (prepared.band.level + 1) := by
          exact (Nat.cast_lt :
            (((prepared.band.band.pointMultiplicity point : ℕ) : ENNReal) <
                ((2 ^ (prepared.band.level + 1) : ℕ) : ENNReal) ↔
              prepared.band.band.pointMultiplicity point <
                2 ^ (prepared.band.level + 1))).mp hupperENN
        simpa [pow_succ, mul_comm] using hupperNat)
      hm24 hdegree

end Kakeya.Assouad.PureWZ2
end
