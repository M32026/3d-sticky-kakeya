module

public import Kakeya.DimensionThree.MainLemma1.Cases

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50RawAmbientBridge

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- A mass comparison plus shade containment controls multiplicity.  This is
the narrow-import version needed before `CaseTwo`. -/
theorem multiplicity_le_mul_of_shade_mass_w50
    {iota : Type u} {s t : Finset iota} (V W : iota -> ShadedBody E) {K : ENNReal}
    (hsub : (⋃ i ∈ t, (W i).shade) ⊆ ⋃ i ∈ s, (V i).shade)
    (hmass : ∑ i ∈ s, volume (V i).shade <=
      K * ∑ i ∈ t, volume (W i).shade) :
    ShadedBody.multiplicity s V <= K * ShadedBody.multiplicity t W := by
  have hK : K * ((∑ i ∈ t, volume (W i).shade) /
      volume (⋃ i ∈ t, (W i).shade)) =
      (K * ∑ i ∈ t, volume (W i).shade) /
        volume (⋃ i ∈ t, (W i).shade) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hK]
  exact ENNReal.div_le_div hmass (measure_mono hsub)

/-- Cardinality retention and fullness give the exact polynomial price for
passing from a retained same-scale subfamily to the ambient family. -/
theorem multiplicity_le_rpow_of_card_fullness_w50
    {delta : NNReal} (hdelta0 : 0 < delta) {iota : Type u} (s t : Finset iota)
    (V : iota -> ShadedTube delta E) (hts : t ⊆ s) (htne : t.Nonempty) {eta q : Real}
    (hcard : (s.card : ENNReal) <=
      (delta : ENNReal) ^ (-q) * (t.card : ENNReal))
    (hfull : (delta : ENNReal) ^ eta <=
      (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) :
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
      (delta : ENNReal) ^ (-(eta + q)) *
        ShadedBody.multiplicity t (fun i => (V i).toShadedBody) := by
  classical
  obtain ⟨i0, hi0⟩ := htne
  let w : ENNReal := volume (V i0).carrier
  have hcar : ∀ r : Finset iota, ∑ i ∈ r, volume (V i).carrier =
      (r.card : ENNReal) * w := by
    intro r
    simpa [w] using Tube.sum_volume_carrier_eq_card_mul
      (fun i => (V i).toTube) (V i0).toTube r
  have hshadeCarrier : ∑ i ∈ s, volume (V i).shade <=
      ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
  have hfullMass : (delta : ENNReal) ^ eta *
      ∑ i ∈ t, volume (V i).carrier <=
      ∑ i ∈ t, volume (V i).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul t
      (fun i => (V i).toShadedBody)]
    exact mul_le_mul_right' hfull _
  have hdeltaNe : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hmass : ∑ i ∈ s, volume (V i).shade <=
      (delta : ENNReal) ^ (-(eta + q)) *
        ∑ i ∈ t, volume (V i).shade := by
    calc
      ∑ i ∈ s, volume (V i).shade <= ∑ i ∈ s, volume (V i).carrier :=
        hshadeCarrier
      _ = (s.card : ENNReal) * w := hcar s
      _ <= ((delta : ENNReal) ^ (-q) * (t.card : ENNReal)) * w :=
        mul_le_mul_right' hcard w
      _ = (delta : ENNReal) ^ (-q) * ∑ i ∈ t, volume (V i).carrier := by
        rw [hcar t]
        ring
      _ = (delta : ENNReal) ^ (-(eta + q)) *
          ((delta : ENNReal) ^ eta * ∑ i ∈ t, volume (V i).carrier) := by
        calc
          (delta : ENNReal) ^ (-q) * ∑ i ∈ t, volume (V i).carrier =
              ((delta : ENNReal) ^ (-q) * 1) *
                ∑ i ∈ t, volume (V i).carrier := by ring
          _ = ((delta : ENNReal) ^ (-(eta + q)) *
                (delta : ENNReal) ^ eta) *
                ∑ i ∈ t, volume (V i).carrier := by
              congr 1
              rw [← ENNReal.rpow_add _ _ hdeltaNe hdeltaTop]
              congr 1
              ring
          _ = (delta : ENNReal) ^ (-(eta + q)) *
                ((delta : ENNReal) ^ eta *
                  ∑ i ∈ t, volume (V i).carrier) := by ring
      _ <= (delta : ENNReal) ^ (-(eta + q)) *
          ∑ i ∈ t, volume (V i).shade := mul_le_mul_left' hfullMass _
  apply multiplicity_le_mul_of_shade_mass_w50
    (fun i => (V i).toShadedBody) (fun i => (V i).toShadedBody)
    (K := (delta : ENNReal) ^ (-(eta + q)))
  · exact Set.iUnion₂_subset fun i hi =>
      Set.subset_iUnion₂ (s := fun i (_ : i ∈ s) => (V i).shade) i (hts hi)
  · exact hmass

/-- The exact ambient-to-retained bridge used by the B3 construction, exposed
without importing `CaseTwo` or any downstream assembly module. -/
theorem eventually_raw_multiplicity_bridge_w50
    (hdim : Module.finrank Real E = 3) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {iota : Type u} (s s2 s' : Finset iota)
        (V : iota -> ShadedTube delta E) (eta : Real),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) ->
        (s : Set iota).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ->
        s2 ⊆ s -> s' ⊆ s2 -> s'.Nonempty ->
        (∀ t ⊆ s2, t.Nonempty ->
          (delta : ENNReal) ^ eta <=
            (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) ->
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) <=
          (delta : ENNReal) ^ (-(eta + 7)) *
            ShadedBody.multiplicity s' (fun i => (V i).toShadedBody) := by
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
    self_mem_nhdsWithin] with delta hcard hdelta0
  intro iota s s2 s' V eta hball hED hs2s hs's2 hs'ne hhered
  have hcardR : (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) :=
    hcard delta le_rfl s (fun i => (V i).toTube) hball hED
  have hcardE : (s.card : ENNReal) <=
      (delta : ENNReal) ^ (-(7 : Real)) * (s'.card : ENNReal) := by
    have hdeltaR : 0 < (delta : Real) := by exact_mod_cast hdelta0
    have hcardE0 : (s.card : ENNReal) <=
        (delta : ENNReal) ^ (-(7 : Real)) := by
      rw [ennreal_coe_nnreal_rpow hdeltaR (-(7 : Real)), ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcardR
    have hs'card : (1 : ENNReal) <= (s'.card : ENNReal) := by
      exact_mod_cast Finset.one_le_card.mpr hs'ne
    calc
      (s.card : ENNReal) <= (delta : ENNReal) ^ (-(7 : Real)) := hcardE0
      _ = (delta : ENNReal) ^ (-(7 : Real)) * 1 := (mul_one _).symm
      _ <= (delta : ENNReal) ^ (-(7 : Real)) * (s'.card : ENNReal) :=
        mul_le_mul_left' hs'card _
  exact multiplicity_le_rpow_of_card_fullness_w50 hdelta0 s s' V
    (hs's2.trans hs2s) hs'ne hcardE (hhered s' hs's2 hs'ne)

end
end Kakeya.ml1Boot.W50RawAmbientBridge
