import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointSimilarity

/-!
# Quantitative raw localization of a Theorem-22-ready common graph
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- The literal paper block before the two affine normalizations. -/
structure WZ1CommonEndpointRawLocalization
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    (ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall) where
  threshold : ℝ := Real.rpow ready.deltaGraph (5 * eta)
  gridScale : ℝ := Real.rpow ready.deltaGraph (6 * eta)
  threshold_eq : threshold = Real.rpow ready.deltaGraph (5 * eta)
  gridScale_eq : gridScale = Real.rpow ready.deltaGraph (6 * eta)
  localized :
    WZ1CommonEndpointLocalizedGraph
      threshold gridScale unitBall.F unitBall.G₁ unitBall.H
  good_half :
    Kakeya.realRpowENN ready.deltaGraph (eta - 3) / 2 ≤
      localized.good.card
  block_threshold :
    Kakeya.realRpowENN ready.deltaGraph (38 * eta - 3) ≤
      (localized.block.card : ENNReal)

/-- The parameter budget turns a ready common graph into the quantitative
paper block. -/
theorem WZ1Lemma23Theorem22ReadyGraph.toRawLocalization
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    (ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall)
    (heta : 0 < eta)
    (hetaSmall : 5 * eta ≤ 1)
    (hcommon : unitBall.G₂ = unitBall.G₁)
    (budget :
      WZ1CommonEndpointParameterBudget eta ready.deltaGraph) :
    Nonempty (WZ1CommonEndpointRawLocalization ready) := by
  let delta := ready.deltaGraph
  let C := Kakeya.realRpowENN delta (-eta)
  let threshold := Real.rpow delta (5 * eta)
  let gridScale := Real.rpow delta (6 * eta)
  have hdelta : 0 < delta := ready.deltaGraph_pos
  have hdeltaOne : delta ≤ 1 := budget.delta_half.trans (by norm_num)
  have hthreshold : 0 < threshold := Real.rpow_pos_of_pos hdelta _
  have hgrid : 0 < gridScale := Real.rpow_pos_of_pos hdelta _
  have hthresholdOne : threshold ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdeltaOne (by positivity)
  have hgridOne : gridScale ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdeltaOne (by positivity)
  have hFkt : unitBall.F.IsKatzTao delta 1 C := by
    simpa [delta, C] using ready.F_katzTao
  have hGkt : unitBall.G₁.IsKatzTao delta 1 C := by
    simpa [delta, C] using ready.G₁_katzTao
  have hsupportCommon :
      ∀ edge ∈ unitBall.H,
        edge.1 ∈ unitBall.F ∧
          edge.2.1 ∈ unitBall.G₁ ∧ edge.2.2 ∈ unitBall.G₁ := by
    intro edge hedge
    have hs := unitBall.edge_support edge hedge
    exact ⟨hs.1, hs.2.1, by simpa [hcommon] using hs.2.2⟩
  have htotal :
      (unitBall.H.card : ENNReal) ≤
        (wz1CommonEndpointGoodEdges threshold unitBall.H).card +
          (C * Kakeya.realRpowENN (threshold / delta) 1) *
            (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 +
          (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 *
            (C * Kakeya.realRpowENN (threshold / delta) 1) := by
    exact common_endpoint_good_edge_lower_bound
      hsupportCommon unitBall.F_unit unitBall.G₁_unit
      hFkt hGkt hdelta hdeltaOne
      (by
        rw [show delta = Real.rpow delta 1 from (Real.rpow_one delta).symm]
        exact Real.rpow_le_rpow_of_exponent_ge
          hdelta hdeltaOne hetaSmall)
      hthresholdOne
  have hbadPower :
      (C * Kakeya.realRpowENN (threshold / delta) 1) *
          (C * Kakeya.realRpowENN (1 / delta) 1) ^ 2 =
        Kakeya.realRpowENN delta (2 * eta - 3) := by
    simpa [C, threshold] using
      (common_endpoint_bad_power_identity (delta := delta) (eta := eta) hdelta)
  have htotal' :
      (unitBall.H.card : ENNReal) ≤
        (wz1CommonEndpointGoodEdges threshold unitBall.H).card +
          Kakeya.realRpowENN delta (2 * eta - 3) +
          Kakeya.realRpowENN delta (2 * eta - 3) := by
    rw [← hbadPower]
    simpa [mul_comm] using htotal
  have hgoodHalf :
      Kakeya.realRpowENN delta (eta - 3) / 2 ≤
        ((wz1CommonEndpointGoodEdges threshold unitBall.H).card : ENNReal) := by
    apply ennreal_half_le_good_of_bad_bound
      (threshold := Kakeya.realRpowENN delta (eta - 3))
      (total := (unitBall.H.card : ENNReal))
      (good :=
        ((wz1CommonEndpointGoodEdges threshold unitBall.H).card : ENNReal))
      (bad := Kakeya.realRpowENN delta (2 * eta - 3))
    · simp [Kakeya.realRpowENN]
    · exact ENNReal.coe_ne_top
    · exact ENNReal.coe_ne_top
    · simp [Kakeya.realRpowENN]
    · exact ready.edge_threshold
    · exact htotal'
    · simpa [delta] using budget.bad_edge_absorb
  rcases wz1_common_endpoint_localize hgrid hgridOne hsupportCommon
      unitBall.F_unit unitBall.G₁_unit with ⟨localized⟩
  have hgoodEq :
      localized.good = wz1CommonEndpointGoodEdges threshold unitBall.H :=
    localized.good_eq
  have hgoodHalf' :
      Kakeya.realRpowENN delta (eta - 3) / 2 ≤
        (localized.good.card : ENNReal) := by
    rw [hgoodEq]
    exact hgoodHalf
  have hgoodReal :
      Real.rpow delta (eta - 3) / 2 ≤
        (localized.good.card : ℝ) := by
    have htopLeft :
        Kakeya.realRpowENN delta (eta - 3) / 2 ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · simp [Kakeya.realRpowENN]
      · norm_num
    have htopRight : (localized.good.card : ENNReal) ≠ ⊤ :=
      ENNReal.coe_ne_top
    have h := (ENNReal.toReal_le_toReal htopLeft htopRight).2 hgoodHalf'
    simpa [Kakeya.realRpowENN, ENNReal.toReal_ofReal,
      Real.rpow_nonneg hdelta.le] using h
  have hgridPower :
      gridScale ^ 6 = Real.rpow delta (36 * eta) := by
    dsimp only [gridScale]
    calc
      (Real.rpow delta (6 * eta)) ^ 6 =
          Real.rpow delta ((6 : ℝ) * (6 * eta)) :=
        rpow_nat_pow hdelta (6 * eta) 6
      _ = Real.rpow delta (36 * eta) := by ring
  have hpowerProduct :
      Real.rpow delta (eta - 3) * Real.rpow delta (36 * eta) =
        Real.rpow delta (37 * eta - 3) := by
    calc
      Real.rpow delta (eta - 3) * Real.rpow delta (36 * eta) =
          Real.rpow delta ((eta - 3) + 36 * eta) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (37 * eta - 3) := by ring
  have hgridBudgetReal :
      2000000 * Real.rpow delta (38 * eta - 3) ≤
        Real.rpow delta (37 * eta - 3) := by
    have hleftTop :
        (2000000 : ENNReal) *
          Kakeya.realRpowENN delta (38 * eta - 3) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN])
    have hrightTop :
        Kakeya.realRpowENN delta (37 * eta - 3) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    have h := (ENNReal.toReal_le_toReal hleftTop hrightTop).2
      budget.grid_loss_absorb
    simpa [Kakeya.realRpowENN, ENNReal.toReal_ofReal,
      Real.rpow_nonneg hdelta.le] using h
  have hquotient :
      Real.rpow delta (38 * eta - 3) ≤
        (localized.good.card : ℝ) /
          (1000000 / gridScale ^ 6) := by
    have hgridPowerPos : 0 < gridScale ^ 6 := by positivity
    have hgoodScaled :
        Real.rpow delta (37 * eta - 3) / 2 ≤
          (localized.good.card : ℝ) * gridScale ^ 6 := by
      calc
        Real.rpow delta (37 * eta - 3) / 2 =
            (Real.rpow delta (eta - 3) / 2) *
              Real.rpow delta (36 * eta) := by
          rw [← hpowerProduct]
          ring
        _ ≤ (localized.good.card : ℝ) *
              Real.rpow delta (36 * eta) := by
          exact mul_le_mul_of_nonneg_right hgoodReal
            (Real.rpow_nonneg hdelta.le _)
        _ = (localized.good.card : ℝ) * gridScale ^ 6 := by
          rw [hgridPower]
    have hdenomPos : 0 < 1000000 / gridScale ^ 6 := by positivity
    apply (le_div_iff₀ hdenomPos).2
    have hscaledBudget :
        Real.rpow delta (38 * eta - 3) * 1000000 ≤
          Real.rpow delta (37 * eta - 3) / 2 := by
      nlinarith [hgridBudgetReal]
    calc
      Real.rpow delta (38 * eta - 3) *
            (1000000 / gridScale ^ 6) =
          (Real.rpow delta (38 * eta - 3) * 1000000) /
            gridScale ^ 6 := by ring
      _ ≤ (Real.rpow delta (37 * eta - 3) / 2) /
            gridScale ^ 6 := by gcongr
      _ ≤ (localized.good.card : ℝ) := by
        apply (div_le_iff₀ hgridPowerPos).2
        simpa [mul_comm] using hgoodScaled
  have hblockReal :
      Real.rpow delta (38 * eta - 3) ≤
        (localized.block.card : ℝ) := by
    calc
      Real.rpow delta (38 * eta - 3) ≤
          (localized.good.card : ℝ) /
            (1000000 / gridScale ^ 6) := hquotient
      _ ≤ (Nat.ceil ((localized.good.card : ℝ) /
          (1000000 / gridScale ^ 6)) : ℝ) := Nat.le_ceil _
      _ ≤ (localized.block.card : ℝ) := by
        exact_mod_cast localized.block_card
  have hblockENN :
      Kakeya.realRpowENN delta (38 * eta - 3) ≤
        (localized.block.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    exact_mod_cast ENNReal.ofReal_le_ofReal hblockReal
  exact ⟨{
    threshold := threshold
    gridScale := gridScale
    threshold_eq := rfl
    gridScale_eq := rfl
    localized := localized
    good_half := by simpa [delta] using hgoodHalf'
    block_threshold := by simpa [delta] using hblockENN
  }⟩

end

end Kakeya.Assouad
