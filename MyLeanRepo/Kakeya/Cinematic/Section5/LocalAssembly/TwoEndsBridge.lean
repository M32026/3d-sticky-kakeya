import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.TangencyBounds
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Combined two-ends localization

This module composes the metric and tangency two-ends inputs. The tangency
parameter is bounded by `4 * t` on a family localized to a `C²` ball of
radius `t`, so the second selection can use that explicit upper scale.
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

structure TwoEndsCertificate
    (I : ParameterInterval)
    (delta diameter epsilon eta t Delta : ℝ)
    (source metricFiber tangencyFiber : FiniteFunctionFamily)
    (center tangencyCenter : C2Function) : Prop where
  delta_le_t : delta ≤ t
  t_le_diameter : t ≤ diameter
  metric_subset :
    metricFiber.carrier ⊆ source.carrier ∩ c2Ball center t
  metric_retention :
    Real.rpow (t / diameter) epsilon * (source.card : ℝ) ≤
      (metricFiber.card : ℝ)
  metric_nonconcentration :
    ∀ g : C2Function, ∀ scale : ℝ,
      delta / t < scale → scale < 1 →
        ((metricFiber.carrier ∩
            c2Ball g (scale * t)).ncard : ℝ) ≤
          4 * Real.rpow (2 * scale) epsilon *
            (metricFiber.card : ℝ)
  delta_le_Delta : delta ≤ Delta
  Delta_le_four_t : Delta ≤ 4 * t
  tangencyCenter_mem : tangencyCenter ∈ metricFiber.carrier
  tangencyFiber_eq :
    tangencyFiber.carrier =
      metricFiber.carrier ∩
        {f | tangencyParameterOn I f tangencyCenter ≤ Delta}
  tangency_retention :
    Real.rpow (Delta / (4 * t)) eta *
        (metricFiber.card : ℝ) ≤
      2 * (tangencyFiber.card : ℝ)
  tangency_nonconcentration :
    ∀ g ∈ metricFiber.carrier,
      ∀ scale : ℝ,
        delta / Delta < scale →
        scale < 1 →
          (((metricFiber.carrier ∩
              {f | tangencyParameterOn I f g ≤
                scale * Delta}).ncard : ℕ) : ℝ) ≤
            2 * Real.rpow scale eta *
              (tangencyFiber.card : ℝ)

theorem localAssembly_two_ends_bridge
    (hMetric : TwoEndsSelectionStatement)
    (hTangency : TangencyTwoEndsSelectionStatement)
    {epsilon eta delta diameter : ℝ}
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hdelta : 0 < delta) (hdelta_diameter : delta ≤ diameter)
    (I : ParameterInterval)
    (F : FiniteFunctionFamily)
    (hF_nonempty : F.carrier.Nonempty)
    (hF_diameter : F.DiameterLE diameter) :
    ∃ t : ℝ, ∃ center : C2Function,
      ∃ G : FiniteFunctionFamily,
        delta ≤ t ∧
        t ≤ diameter ∧
        G.carrier ⊆ F.carrier ∩ c2Ball center t ∧
        Real.rpow (t / diameter) epsilon * (F.card : ℝ) ≤
          (G.card : ℝ) ∧
        (∀ g : C2Function, ∀ scale : ℝ,
          delta / t < scale → scale < 1 →
            ((G.carrier ∩ c2Ball g (scale * t)).ncard : ℝ) ≤
              4 * Real.rpow (2 * scale) epsilon * (G.card : ℝ)) ∧
        ∃ Delta : ℝ, ∃ k : C2Function,
          ∃ H : FiniteFunctionFamily,
            delta ≤ Delta ∧
            Delta ≤ 4 * t ∧
            k ∈ G.carrier ∧
            H.carrier =
              G.carrier ∩
                {f | tangencyParameterOn I f k ≤ Delta} ∧
            Real.rpow (Delta / (4 * t)) eta * (G.card : ℝ) ≤
              2 * (H.card : ℝ) ∧
            ∀ g ∈ G.carrier,
              ∀ scale : ℝ,
                delta / Delta < scale →
                scale < 1 →
                (((G.carrier ∩
                    {f | tangencyParameterOn I f g ≤
                      scale * Delta}).ncard : ℕ) : ℝ) ≤
                  2 * Real.rpow scale eta * (H.card : ℝ) := by
  rcases hMetric epsilon delta diameter hepsilon hdelta hdelta_diameter
      F hF_nonempty hF_diameter with
    ⟨t, center, G, hdelta_t, ht_diameter, hG_sub,
      hG_retention, hG_nonconcentration⟩
  have ht_pos : 0 < t := hdelta.trans_le hdelta_t
  have hG_card_pos : 0 < (G.card : ℝ) := by
    have hF_card_pos : 0 < (F.card : ℝ) := by
      have h : 0 < F.carrier.ncard :=
        (Set.ncard_pos F.finite).2 hF_nonempty
      exact_mod_cast h
    have hfactor_pos :
        0 < Real.rpow (t / diameter) epsilon := by
      have hdiameter_pos : 0 < diameter :=
        hdelta.trans_le hdelta_diameter
      exact Real.rpow_pos_of_pos (div_pos ht_pos hdiameter_pos) _
    have hleft :
        0 < Real.rpow (t / diameter) epsilon * (F.card : ℝ) :=
      mul_pos hfactor_pos hF_card_pos
    exact hleft.trans_le hG_retention
  have hG_nonempty : G.carrier.Nonempty := by
    have hG_nat_pos : 0 < G.card := by exact_mod_cast hG_card_pos
    exact (Set.ncard_pos G.finite).1 hG_nat_pos
  have hG_ball : G.carrier ⊆ c2Ball center t :=
    fun f hf => (hG_sub hf).2
  have htangency :
      ∀ ⦃f⦄, f ∈ G.carrier →
        ∀ ⦃g⦄, g ∈ G.carrier →
          0 ≤ tangencyParameterOn I f g ∧
            tangencyParameterOn I f g ≤ 4 * t :=
    localAssembly_tangency_bounds_of_localized hG_ball
  have hdelta_four_t : delta ≤ 4 * t := by
    linarith
  rcases hTangency eta delta (4 * t) heta hdelta hdelta_four_t
      I G hG_nonempty htangency with
    ⟨Delta, k, H, hdelta_Delta, hDelta, hk, hH,
      hH_retention, hH_nonconcentration⟩
  exact
    ⟨t, center, G, hdelta_t, ht_diameter, hG_sub,
      hG_retention, hG_nonconcentration,
      Delta, k, H, hdelta_Delta, hDelta, hk, hH,
      hH_retention, hH_nonconcentration⟩

theorem localAssembly_two_ends_bridge_with_certificate
    (hMetric : TwoEndsSelectionStatement)
    (hTangency : TangencyTwoEndsSelectionStatement)
    {epsilon eta delta diameter : ℝ}
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hdelta : 0 < delta) (hdelta_diameter : delta ≤ diameter)
    (I : ParameterInterval)
    (F : FiniteFunctionFamily)
    (hF_nonempty : F.carrier.Nonempty)
    (hF_diameter : F.DiameterLE diameter) :
    ∃ t center G Delta k H,
      TwoEndsCertificate I delta diameter epsilon eta t Delta
        F G H center k := by
  rcases localAssembly_two_ends_bridge hMetric hTangency
      hepsilon heta hdelta hdelta_diameter I F
      hF_nonempty hF_diameter with
    ⟨t, center, G, hdelta_t, ht_diameter, hG_sub,
      hG_retention, hG_nonconcentration,
      Delta, k, H, hdelta_Delta, hDelta, hk, hH,
      hH_retention, hH_nonconcentration⟩
  exact
    ⟨t, center, G, Delta, k, H,
      ⟨hdelta_t, ht_diameter, hG_sub,
        hG_retention, hG_nonconcentration,
        hdelta_Delta, hDelta, hk, hH,
        hH_retention, hH_nonconcentration⟩⟩

end Kakeya.Cinematic
