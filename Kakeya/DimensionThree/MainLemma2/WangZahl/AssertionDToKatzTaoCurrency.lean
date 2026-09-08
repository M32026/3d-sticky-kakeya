module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD

@[expose] public section

open MeasureTheory Filter Topology

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The model `delta`-tube has the scale-normalized power required by the
`AssertionD -> KKT` cancellation.  All dimensional constants are isolated in
the explicit absorption hypothesis. -/
theorem tubeVolume_rpow_le_scale
    {delta kappa : ENNReal} {gamma epsilon : Real}
    (hgamma : 0 <= gamma) (hdelta0 : delta ≠ 0) (hdeltaTop : delta ≠ ⊤)
    (hvol : tubeVolume delta.toNNReal <=
      (Tube.volume_le.C 3 : ENNReal) * delta ^ (2 : Real))
    (habsorb : (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2) <=
      kappa * delta ^ (-epsilon / 2)) :
    (tubeVolume delta.toNNReal) ^ (gamma / 2) <=
      kappa * delta ^ (gamma - epsilon / 2) := by
  have hhalf : 0 <= gamma / 2 := by positivity
  calc
    (tubeVolume delta.toNNReal) ^ (gamma / 2) <=
        ((Tube.volume_le.C 3 : ENNReal) * delta ^ (2 : Real)) ^ (gamma / 2) :=
      ENNReal.rpow_le_rpow hvol hhalf
    _ = (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2) * delta ^ gamma := by
      rw [ENNReal.mul_rpow_of_ne_zero
        (by exact_mod_cast (Tube.volume_le.C_pos 3).ne')
        (by simp [ENNReal.rpow_eq_zero_iff, hdelta0, hdeltaTop]),
        <- ENNReal.rpow_mul]
      congr 1
      ring
    _ <= (kappa * delta ^ (-epsilon / 2)) * delta ^ gamma := by gcongr
    _ = kappa * delta ^ (gamma - epsilon / 2) := by
      rw [mul_assoc, <- ENNReal.rpow_add _ _ hdelta0 hdeltaTop]
      congr 1
      ring

/-- Concrete specialization of `tubeVolume_rpow_le_scale` to the model tube
at a small scale. -/
theorem tubeVolume_rpow_le_scale_of_coe
    {delta : NNReal} {kappa : ENNReal} {gamma epsilon : Real}
    (hgamma : 0 <= gamma) (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (habsorb : (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2) <=
      kappa * (delta : ENNReal) ^ (-epsilon / 2)) :
    (tubeVolume delta) ^ (gamma / 2) <=
      kappa * (delta : ENNReal) ^ (gamma - epsilon / 2) := by
  apply tubeVolume_rpow_le_scale hgamma
    (ENNReal.coe_ne_zero.mpr hdelta0.ne') ENNReal.coe_ne_top
  · simpa [tubeVolume] using Tube.volume_le hdelta1 (modelTube delta)
  · exact habsorb

/-- Any finite WZ normalization constant is eventually absorbed by a negative
power of the scale. -/
theorem eventually_finite_le_rpow_neg_wz {c : ENNReal} (hc : c ≠ ⊤)
    {a : Real} (ha : 0 < a) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      c <= (delta : ENNReal) ^ (-a) := by
  by_cases hc0 : c = 0
  · subst c
    exact Filter.Eventually.of_forall fun delta => by simp
  let cutoff : NNReal := c.toNNReal⁻¹ ^ (1 / a)
  have hcinv : 0 < c.toNNReal⁻¹ := by
    exact inv_pos.mpr (ENNReal.toNNReal_pos hc0 hc)
  have hcutoff : 0 < cutoff := NNReal.rpow_pos hcinv
  filter_upwards [Ioo_mem_nhdsGT hcutoff] with delta hdelta
  have hdelta_cutoff : delta <= cutoff := hdelta.2.le
  have hcutoff_pow : cutoff ^ a = c.toNNReal⁻¹ := by
    calc
      cutoff ^ a = (c.toNNReal⁻¹ ^ (1 / a)) ^ a := by rfl
      _ = c.toNNReal⁻¹ ^ ((1 / a) * a) := by
        rw [<- NNReal.rpow_mul]
      _ = c.toNNReal⁻¹ := by
        rw [one_div_mul_cancel ha.ne', NNReal.rpow_one]
  have hdelta_pow : (delta : ENNReal) ^ a <= c⁻¹ := by
    calc
      (delta : ENNReal) ^ a <= (cutoff : ENNReal) ^ a := by
        exact ENNReal.rpow_le_rpow (by exact_mod_cast hdelta_cutoff) ha.le
      _ = ((cutoff ^ a : NNReal) : ENNReal) := by
        rw [<- ENNReal.coe_rpow_of_nonneg cutoff ha.le]
      _ = ((c.toNNReal⁻¹ : NNReal) : ENNReal) := by rw [hcutoff_pow]
      _ = c⁻¹ := by
        rw [ENNReal.coe_inv (ENNReal.toNNReal_pos hc0 hc).ne',
          ENNReal.coe_toNNReal hc]
  have hcc : c * c⁻¹ <= 1 := by
    rw [ENNReal.mul_inv_cancel hc0 hc]
  rw [ENNReal.rpow_neg]
  refine ENNReal.le_inv_iff_mul_le.mpr ?_
  calc
    c * (delta : ENNReal) ^ a <= c * c⁻¹ := by gcongr
    _ <= 1 := hcc

/-- The model-tube scale normalization holds automatically at all sufficiently
small scales; this removes the last numerical premise from the
`AssertionD -> KKT` conversion. -/
theorem eventually_tubeVolume_rpow_le_scale
    {kappa : NNReal} {gamma epsilon : Real}
    (hgamma : 0 <= gamma) (hepsilon : 0 < epsilon) (hkappa : 0 < kappa) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      (tubeVolume delta) ^ (gamma / 2) <=
        (kappa : ENNReal) * (delta : ENNReal) ^ (gamma - epsilon / 2) := by
  let C : ENNReal := (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2)
  let c : ENNReal := C * (kappa : ENNReal)⁻¹
  have hCtop : C ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top hCtop (by simp [hkappa.ne'])
  filter_upwards [eventually_finite_le_rpow_neg_wz hctop (half_pos hepsilon),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta habs hdelta
  have hdelta0 : 0 < delta := hdelta.1
  have hdelta1 : delta <= 1 := hdelta.2.le
  have habs' : c <= (delta : ENNReal) ^ (-epsilon / 2) := by
    convert habs using 1 <;> ring
  have habsorb : C <= (kappa : ENNReal) * (delta : ENNReal) ^ (-epsilon / 2) := by
    calc
      C = (kappa : ENNReal) * c := by
        dsimp [c]
        symm
        calc
          (kappa : ENNReal) * (C * (kappa : ENNReal)⁻¹) =
              C * ((kappa : ENNReal) * (kappa : ENNReal)⁻¹) := by ring
          _ = C := by
            rw [ENNReal.mul_inv_cancel
              (ENNReal.coe_ne_zero.mpr hkappa.ne') ENNReal.coe_ne_top, mul_one]
      _ <= (kappa : ENNReal) * (delta : ENNReal) ^ (-epsilon / 2) := by gcongr
  exact tubeVolume_rpow_le_scale_of_coe hgamma hdelta0 hdelta1 (by
    simpa [C] using habsorb)

/-- The exact algebraic cancellation in the `AssertionD (gamma,gamma)` to
Katz--Tao currency conversion.  The only geometric input left in this lemma is
the scale-normalized upper bound on the model tube volume. -/
theorem assertionD_coefficient_cancels
    {delta kappa A V U : ENNReal} {gamma epsilon : Real}
    (hgamma : 0 <= gamma) (hdelta0 : delta ≠ 0) (hdeltaTop : delta ≠ ⊤)
    (hA0 : A ≠ 0) (hATop : A ≠ ⊤) (hV0 : V ≠ 0) (hVTop : V ≠ ⊤)
    (hkappa0 : kappa ≠ 0) (hkappaTop : kappa ≠ ⊤)
    (hscale : V ^ (gamma / 2) <=
      kappa * delta ^ (gamma - epsilon / 2))
    (hD : kappa * delta ^ (gamma + epsilon / 2) * A * V *
        (A * V ^ (1 / 2 : Real)) ^ (-gamma) <= U) :
    A * V <= delta ^ (-epsilon) * A ^ gamma * U := by
  have hAhalf0 : A * V ^ (1 / 2 : Real) ≠ 0 := by
    refine mul_ne_zero hA0 ?_
    simp [ENNReal.rpow_eq_zero_iff, hV0, hVTop]
  have hAhalfTop : A * V ^ (1 / 2 : Real) ≠ ⊤ := by
    exact ENNReal.mul_ne_top hATop
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVTop)
  have hfactor :
      (A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma =
        (V ^ (gamma / 2))⁻¹ := by
    rw [ENNReal.rpow_neg, ENNReal.mul_rpow_of_ne_zero hA0
      (by simp [ENNReal.rpow_eq_zero_iff, hV0, hVTop])]
    rw [ENNReal.mul_inv
      (Or.inl (by simp [ENNReal.rpow_eq_zero_iff, hA0, hATop]))
      (Or.inl (by simp [ENNReal.rpow_eq_top_iff, hA0, hATop]))]
    rw [show (V ^ (1 / 2 : Real)) ^ gamma = V ^ (gamma / 2) by
      rw [<- ENNReal.rpow_mul]
      congr 1
      ring]
    calc
      (A ^ gamma)⁻¹ * (V ^ (gamma / 2))⁻¹ * A ^ gamma =
          ((A ^ gamma)⁻¹ * A ^ gamma) * (V ^ (gamma / 2))⁻¹ := by ring
      _ = (V ^ (gamma / 2))⁻¹ := by
        rw [ENNReal.inv_mul_cancel
          (by simp [ENNReal.rpow_eq_zero_iff, hA0, hATop])
          (ENNReal.rpow_ne_top_of_nonneg hgamma hATop), one_mul]
  have hcoeff :
      delta ^ epsilon <= kappa * delta ^ (gamma + epsilon / 2) *
        (A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma := by
    have hY0 : kappa * delta ^ (gamma - epsilon / 2) ≠ 0 := by
      refine mul_ne_zero hkappa0 ?_
      simp [ENNReal.rpow_eq_zero_iff, hdelta0, hdeltaTop]
    have hYTop : kappa * delta ^ (gamma - epsilon / 2) ≠ ⊤ := by
      refine ENNReal.mul_ne_top hkappaTop ?_
      simp [ENNReal.rpow_eq_top_iff, hdelta0, hdeltaTop]
    have hX0 : V ^ (gamma / 2) ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hV0, hVTop]
    have hXTop : V ^ (gamma / 2) ≠ ⊤ := by
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hVTop
    have hinv : (kappa * delta ^ (gamma - epsilon / 2))⁻¹ <=
        (V ^ (gamma / 2))⁻¹ := ENNReal.inv_le_inv.mpr hscale
    have hratio : (kappa * delta ^ (gamma - epsilon / 2))⁻¹ *
        (kappa * delta ^ (gamma + epsilon / 2)) = delta ^ epsilon := by
      rw [ENNReal.mul_inv (Or.inl hkappa0) (Or.inl hkappaTop)]
      calc
        (kappa⁻¹ * (delta ^ (gamma - epsilon / 2))⁻¹) *
            (kappa * delta ^ (gamma + epsilon / 2)) =
            (kappa⁻¹ * kappa) *
              ((delta ^ (gamma - epsilon / 2))⁻¹ *
                delta ^ (gamma + epsilon / 2)) := by ring
        _ = (delta ^ (gamma - epsilon / 2))⁻¹ *
              delta ^ (gamma + epsilon / 2) := by
            rw [ENNReal.inv_mul_cancel hkappa0 hkappaTop, one_mul]
        _ = delta ^ epsilon := by
            rw [<- ENNReal.rpow_neg,
              <- ENNReal.rpow_add _ _ hdelta0 hdeltaTop]
            congr 1
            ring
    calc
      delta ^ epsilon = (kappa * delta ^ (gamma - epsilon / 2))⁻¹ *
          (kappa * delta ^ (gamma + epsilon / 2)) := hratio.symm
      _ <= (V ^ (gamma / 2))⁻¹ *
          (kappa * delta ^ (gamma + epsilon / 2)) := by gcongr
      _ = kappa * delta ^ (gamma + epsilon / 2) *
          (A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma := by
        calc
          (V ^ (gamma / 2))⁻¹ *
              (kappa * delta ^ (gamma + epsilon / 2)) =
              (kappa * delta ^ (gamma + epsilon / 2)) *
                (V ^ (gamma / 2))⁻¹ := by ring
          _ = (kappa * delta ^ (gamma + epsilon / 2)) *
                ((A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma) := by
              rw [hfactor]
          _ = kappa * delta ^ (gamma + epsilon / 2) *
                (A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma := by ring
  have hscaled := mul_le_mul_right' hD (delta ^ (-epsilon) * A ^ gamma)
  calc
    A * V = delta ^ (-epsilon) * delta ^ epsilon * (A * V) := by
      rw [<- ENNReal.rpow_add _ _ hdelta0 hdeltaTop]
      simp
    _ <= delta ^ (-epsilon) *
        (kappa * delta ^ (gamma + epsilon / 2) *
          (A * V ^ (1 / 2 : Real)) ^ (-gamma) * A ^ gamma) * (A * V) := by
      gcongr
    _ = (kappa * delta ^ (gamma + epsilon / 2) * A * V *
          (A * V ^ (1 / 2 : Real)) ^ (-gamma)) *
        (delta ^ (-epsilon) * A ^ gamma) := by ring
    _ <= U * (delta ^ (-epsilon) * A ^ gamma) := hscaled
    _ = delta ^ (-epsilon) * A ^ gamma * U := by ring

/-- End-to-end exponent and model-volume conversion for one family.  This is
the exact numerical conclusion required by `KatzTaoEstimate`; constructing a
family to which `AssertionD` applies is deliberately the only upstream
geometric obligation not present here. -/
theorem assertionD_bound_implies_katzTao_mass
    {delta : NNReal} {iota : Type u} (s : Finset iota)
    (T : iota -> ShadedTube delta Space3)
    {kappa : NNReal} {gamma epsilon : Real}
    (hgamma : 0 <= gamma) (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hs : s.Nonempty) (hkappa : 0 < kappa)
    (habsorb : (Tube.volume_le.C 3 : ENNReal) ^ (gamma / 2) <=
      (kappa : ENNReal) * (delta : ENNReal) ^ (-epsilon / 2))
    (hD : (kappa : ENNReal) * (delta : ENNReal) ^ (gamma + epsilon / 2) *
        (s.card : ENNReal) * tubeVolume delta *
          (((s.card : ENNReal) * tubeVolume delta ^ (1 / 2 : Real)) ^ (-gamma)) <=
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) :
    (s.card : ENNReal) * tubeVolume delta <=
      (delta : ENNReal) ^ (-epsilon) * (s.card : ENNReal) ^ gamma *
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  have hcard0 : (s.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hs).ne'
  have hcardTop : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hvol := tubeVolume_pos_and_ne_top hdelta0
  apply assertionD_coefficient_cancels hgamma
    (ENNReal.coe_ne_zero.mpr hdelta0.ne') ENNReal.coe_ne_top
    hcard0 hcardTop hvol.1.ne' hvol.2
    (ENNReal.coe_ne_zero.mpr hkappa.ne') ENNReal.coe_ne_top
  · exact tubeVolume_rpow_le_scale_of_coe hgamma hdelta0 hdelta1 habsorb
  · exact hD

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.tubeVolume_rpow_le_scale
#print axioms Kakeya.WangZahl.tubeVolume_rpow_le_scale_of_coe
#print axioms Kakeya.WangZahl.eventually_finite_le_rpow_neg_wz
#print axioms Kakeya.WangZahl.eventually_tubeVolume_rpow_le_scale
#print axioms Kakeya.WangZahl.assertionD_coefficient_cancels
#print axioms Kakeya.WangZahl.assertionD_bound_implies_katzTao_mass
