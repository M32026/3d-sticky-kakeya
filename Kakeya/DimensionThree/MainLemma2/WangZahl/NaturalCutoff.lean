module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.AssertionDToKatzTaoCurrency
public import Kakeya.DimensionThree.MainLemma2.WangZahl.AssertionDInputBundle

@[expose] public section

open MeasureTheory Filter Topology

namespace Kakeya.WangZahl

noncomputable section

/-- A finite dimensional constant times `delta^-eta` admits a natural ceiling
whose extra integer rounding is absorbed by one further `delta^-eta`. -/
theorem eventually_exists_nat_degree_cutoff {c : ENNReal} (hc : c ≠ ⊤)
    {eta : Real} (heta : 0 < eta) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∃ M : Nat,
        c * (delta : ENNReal) ^ (-eta) <= (M : ENNReal) ∧
        ((M : ENNReal) + 1) <= (delta : ENNReal) ^ (-(2 * eta)) := by
  let c2 : ENNReal := c + 2
  have hc2top : c2 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hc, by simp⟩
  filter_upwards [eventually_finite_le_rpow_neg_wz hc2top heta,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hc2 ⟨hdelta0, hdelta1⟩
  let x : ENNReal := c * (delta : ENNReal) ^ (-eta)
  have hxtop : x ≠ ⊤ := ENNReal.mul_ne_top hc
    (by simp [ENNReal.rpow_eq_top_iff, ENNReal.coe_ne_zero.mpr hdelta0.ne',
      ENNReal.coe_ne_top])
  let M : Nat := Nat.ceil x.toReal
  refine ⟨M, ?_, ?_⟩
  · change x <= (M : ENNReal)
    rw [<- ENNReal.ofReal_toReal hxtop]
    calc
      ENNReal.ofReal x.toReal <= ENNReal.ofReal (M : Real) :=
        ENNReal.ofReal_mono (by simpa [M] using Nat.le_ceil x.toReal)
      _ = (M : ENNReal) := by rw [ENNReal.ofReal_natCast]
  · have hceil : (M : ENNReal) <= x + 1 := by
      have hr : (M : Real) <= x.toReal + 1 := by
        simpa [M] using (Nat.ceil_lt_add_one ENNReal.toReal_nonneg).le
      calc
        (M : ENNReal) = ENNReal.ofReal (M : Real) := by
          rw [ENNReal.ofReal_natCast]
        _ <= ENNReal.ofReal (x.toReal + 1) := ENNReal.ofReal_mono hr
        _ = ENNReal.ofReal x.toReal + 1 := by
          rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
            ENNReal.ofReal_one]
        _ = x + 1 := by rw [ENNReal.ofReal_toReal hxtop]
    have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-eta) := by
      rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
      exact ENNReal.rpow_le_one (by exact_mod_cast hdelta1.le) heta.le
    calc
      (M : ENNReal) + 1 <= x + 2 := by
        calc
          (M : ENNReal) + 1 <= (x + 1) + 1 := add_le_add_left hceil 1
          _ = x + 2 := by norm_num [add_assoc]
      _ <= (c + 2) * (delta : ENNReal) ^ (-eta) := by
        dsimp [x]
        calc
          c * (delta : ENNReal) ^ (-eta) + 2 <=
              c * (delta : ENNReal) ^ (-eta) +
                2 * (delta : ENNReal) ^ (-eta) := by
            simpa using add_le_add_right (mul_le_mul_left' hone (2 : ENNReal))
              (c * (delta : ENNReal) ^ (-eta))
          _ = (c + 2) * (delta : ENNReal) ^ (-eta) := by ring
      _ <= (delta : ENNReal) ^ (-eta) *
          (delta : ENNReal) ^ (-eta) := by gcongr
      _ = (delta : ENNReal) ^ (-(2 * eta)) := by
        rw [<- ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hdelta0.ne')
          ENNReal.coe_ne_top]
        congr 1
        ring

/-- The usable exponent budget: a degree cap of order `delta^-eta` has natural
rounding loss `delta^-2eta`; after selection, all Assertion D inputs hold at
the common exponent `4*eta`. -/
theorem exists_assertionD_input_subfamily_four_eta
    {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {eta : Real} (heta : 0 < eta)
    {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3)
    (hs : s.Nonempty) {M : Nat}
    (hMdegree : Tube.refineToEssDistinctLeaves.C 3 *
        (delta : ENNReal) ^ (-eta) <= (M : ENNReal))
    (hMloss : ((M : ENNReal) + 1) <= (delta : ENNReal) ^ (-(2 * eta)))
    (hmax : maxDensity s (fun i => (T i).toConvexSpaceBody) <=
      (delta : ENNReal) ^ (-eta))
    (hKT : ConvexSpaceBody.IsKatzTao s
      (fun i => (T i).toConvexSpaceBody) ((delta : ENNReal) ^ (-eta)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hF : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3))
      ((delta : ENNReal) ^ (-eta)))
    (hdense : (delta : ENNReal) ^ eta *
        (∑ i ∈ s, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).shade) :
    ∃ t : Finset iota, t ⊆ s ∧ IsTubeShadingFamily t T ∧
      (∑ i ∈ s, volume (T i).shade) <=
        (((M : ENNReal) + 1) * ∑ i ∈ t, volume (T i).shade) ∧
      IsDense t T
        ⟨(delta : Real) ^ (4 * eta), Real.rpow_nonneg delta.coe_nonneg _⟩ ∧
      katzTaoConvexWolffConstant t T <=
        (delta : ENNReal) ^ (-(4 * eta)) ∧
      frostmanSlabWolffConstant t T <=
        (delta : ENNReal) ^ (-(4 * eta)) := by
  classical
  let d : ENNReal := (delta : ENNReal)
  let L : ENNReal := (M : ENNReal) + 1
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdtop : d ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : d <= 1 := by simpa [d] using ENNReal.coe_le_coe.mpr hdelta1
  have hdetatop : d ^ eta ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg' (ENNReal.coe_pos.mpr hdelta) hdtop
  obtain ⟨t, ht, hfamily, hshade, hdenseRaw, hFraw, hKTRaw, hslabRaw⟩ :=
    exists_assertionD_input_subfamily hdelta hdelta1 s T hs hmax hMdegree
      hKT (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) hdtop)
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) hdtop)
      hdetatop hball hF hdense
  have hInvLoss : d ^ (2 * eta) <= L⁻¹ := by
    have hinv := ENNReal.inv_le_inv.mpr (by simpa [d, L] using hMloss)
    rw [<- ENNReal.rpow_neg] at hinv
    simpa [d, L] using hinv
  have hDenseCoeff : d ^ (4 * eta) <= d ^ eta * L⁻¹ := by
    calc
      d ^ (4 * eta) <= d ^ (3 * eta) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ = d ^ eta * d ^ (2 * eta) := by
        rw [<- ENNReal.rpow_add eta (2 * eta) hd0 hdtop]
        congr 1 <;> ring
      _ <= d ^ eta * L⁻¹ := by gcongr
  have hdenseFinal : IsDense t T
      ⟨(delta : Real) ^ (4 * eta), Real.rpow_nonneg delta.coe_nonneg _⟩ := by
    rw [IsDense]
    let q : NNReal :=
      ⟨(delta : Real) ^ (4 * eta), Real.rpow_nonneg delta.coe_nonneg _⟩
    have hcoe : (q : ENNReal) = d ^ (4 * eta) := by
      rw [ennreal_coe_nnreal_rpow (by exact_mod_cast hdelta)]
      calc
        (q : ENNReal) = ENNReal.ofReal (q : Real) := ENNReal.coe_nnreal_eq q
        _ = ENNReal.ofReal ((delta : Real) ^ (4 * eta)) := by rfl
    change (q : ENNReal) * (∑ i ∈ t, volume (T i).carrier) <=
      ∑ i ∈ t, volume (T i).shade
    rw [hcoe]
    exact (mul_le_mul_right' hDenseCoeff
      (∑ i ∈ t, volume (T i).carrier)).trans (by simpa [d, L] using hdenseRaw)
  have hKTFinal : katzTaoConvexWolffConstant t T <= d ^ (-(4 * eta)) :=
    hKTRaw.trans (ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith))
  have hConst : d ^ (-eta) * ((d ^ eta)⁻¹ * L) <= d ^ (-(4 * eta)) := by
    have hL : L <= d ^ (-(2 * eta)) := by simpa [d, L] using hMloss
    rw [show (d ^ eta)⁻¹ = d ^ (-eta) by rw [ENNReal.rpow_neg]]
    calc
      d ^ (-eta) * (d ^ (-eta) * L) <=
          d ^ (-eta) * (d ^ (-eta) * d ^ (-(2 * eta))) := by gcongr
      _ = d ^ (-(4 * eta)) := by
        rw [<- ENNReal.rpow_add (-eta) (-(2 * eta)) hd0 hdtop,
          <- ENNReal.rpow_add (-eta) (-eta + -(2 * eta)) hd0 hdtop]
        congr 1 <;> ring
  have hslabFinal : frostmanSlabWolffConstant t T <= d ^ (-(4 * eta)) :=
    hslabRaw.trans (by simpa [d, L] using hConst)
  exact ⟨t, ht, hfamily, hshade, hdenseFinal,
    by simpa [d] using hKTFinal, by simpa [d] using hslabFinal⟩

/-- Pull a Katz--Tao mass estimate on the selected family back to the original
family, paying exactly the shade-selection factor and using monotonicity of the
shade union. -/
theorem katzTao_mass_pullback_of_shade_selection
    {delta : NNReal} {iota : Type u} {s t : Finset iota}
    (T : iota -> ShadedTube delta Space3) (ht : t ⊆ s)
    {L R : ENNReal} {gamma : Real}
    (hgamma : 0 <= gamma)
    (hshade : (∑ i ∈ s, volume (T i).shade) <=
      L * ∑ i ∈ t, volume (T i).shade)
    (hmass : (t.card : ENNReal) * tubeVolume delta <=
      R * (t.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade t fun i => (T i).toShadedBody)) :
    (∑ i ∈ s, volume (T i).shade) <=
      L * R * (s.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  have hsumt : (∑ i ∈ t, volume (T i).shade) <=
      (t.card : ENNReal) * tubeVolume delta := by
    calc
      (∑ i ∈ t, volume (T i).shade) <=
          ∑ i ∈ t, volume (T i).carrier :=
        Finset.sum_le_sum fun i hi => measure_mono (T i).shade_subset
      _ = ∑ _i ∈ t, tubeVolume delta :=
        Finset.sum_congr rfl fun i hi => volume_carrier_eq_tubeVolume T i
      _ = (t.card : ENNReal) * tubeVolume delta := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (t.card : ENNReal) ^ gamma <= (s.card : ENNReal) ^ gamma := by
    exact ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card ht) hgamma
  have hunion : volume (ShadedBody.iUnionShade t fun i => (T i).toShadedBody) <=
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
    apply measure_mono
    exact Set.iUnion₂_subset fun i hi =>
      Set.subset_biUnion_of_mem (u := fun j => (T j).shade) (ht hi)
  calc
    (∑ i ∈ s, volume (T i).shade) <=
        L * ∑ i ∈ t, volume (T i).shade := hshade
    _ <= L * ((t.card : ENNReal) * tubeVolume delta) := by gcongr
    _ <= L * (R * (t.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade t fun i => (T i).toShadedBody)) := by
      exact mul_le_mul_left' hmass L
    _ = L * R * (t.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade t fun i => (T i).toShadedBody) := by ring
    _ <= L * R * (s.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
      exact mul_le_mul'
        (mul_le_mul_left' hcard (L * R)) hunion

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.eventually_exists_nat_degree_cutoff
#print axioms Kakeya.WangZahl.exists_assertionD_input_subfamily_four_eta
#print axioms Kakeya.WangZahl.katzTao_mass_pullback_of_shade_selection
