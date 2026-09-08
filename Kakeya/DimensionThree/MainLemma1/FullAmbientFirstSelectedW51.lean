module

public import Kakeya.DimensionThree.MainLemma1.OneScaleNoUnif
public import Kakeya.DimensionThree.MainLemma1.LossLedger

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51FullAmbientFirst

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- A full-ambient first pass with the exact one-scale loss.  Positive total
shade mass is sufficient: the density parameter in the raw one-scale producer
is set to zero, while its selected-fibre averaging still retains the genuine
ambient fullness. -/
theorem exists_firstSelected_fullAmbient_w51
    (hdim : Module.finrank Real E = 3)
    {delta tau : NNReal} (hdelta0 : 0 < delta)
    (hdeltaTau : delta <= tau) (htau1 : tau <= 1)
    {iota kappa : Type u} [DecidableEq iota] [DecidableEq kappa]
    {s : Finset iota} {tTau : Finset kappa}
    (V : iota -> ShadedTube delta E) (TTau : kappa -> Tube tau E)
    (pTau : iota -> kappa)
    (hball : forall i, i ∈ s -> (V i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily s (fun i => (V i).toTube)
      tTau TTau pTau)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    exists (act' : Finset iota) (Z' : iota -> ShadedTube delta E)
      (tAct : Finset kappa) (ZTau : kappa -> ShadedTube tau E)
      (kF : kappa) (lamF : NNReal),
      IsOneScaleSelected
        (((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal)
        ((factorOneScale.C s.card delta : NNReal) : ENNReal)
        s s V tTau TTau pTau act' Z' tAct ZTau kF 0 lamF := by
  classical
  have hsne : s.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs] at hmass
  have hcarrier : ∑ i ∈ s, volume (V i).carrier ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    exact ne_of_gt ((tube_volume_pos_ne_top (E := E) hdelta0 (V i).toTube).1.trans_le
      (Finset.single_le_sum (f := fun j => volume (V j).carrier)
        (fun _ _ => by positivity) hi))
  obtain ⟨act', Z', tAct, ZTau, kF, lamF, hsel⟩ :=
    exists_isOneScaleSelected_of_dens (E := E) hdim hdelta0 hdeltaTau htau1
      (amb := s) (act := s) (hact := fun _ hi => hi)
      V TTau pTau
      (hoff := fun i hi hnot => False.elim (hnot hi)) hball
      (lam := 0) (Cd := 1) (by norm_num)
      (hdens := by intro i hi; simp) hcarrier hparent hmass
  refine ⟨act', Z', tAct, ZTau, kF, lamF, ?_⟩
  simpa using hsel

/-- Raw CaseTwo hypotheses produce the full-ambient endpoint first pass.  This
uses `tau = delta`, the identity parent family, and exactly
`factorOneScale.C s.card delta` as the scalar loss. -/
theorem exists_caseTwo_fullAmbient_endpoint_firstSelected_w51
    (hdim : Module.finrank Real E = 3)
    {p : Params} {delta : NNReal} (hdelta0 : 0 < delta)
    (hdelta1 : delta <= 1)
    {iota : Type u} [DecidableEq iota]
    {s s2 : Finset iota} (V : iota -> ShadedTube delta E)
    (hball : forall i, i ∈ s -> (V i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier))
    (hs2s : s2 ⊆ s) (hs2ne : s2.Nonempty)
    (hhered : forall t, t ⊆ s2 -> t.Nonempty ->
      (delta : ENNReal) ^ p.η 0 <=
        (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) :
    exists (act' : Finset iota) (Z' : iota -> ShadedTube delta E)
      (tAct : Finset iota) (ZTau : iota -> ShadedTube delta E)
      (kF : iota) (lamF : NNReal),
      IsOneScaleSelected
        (((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal)
        ((factorOneScale.C s.card delta : NNReal) : ENNReal)
        s s V s (fun i => (V i).toTube) id
        act' Z' tAct ZTau kF 0 lamF := by
  have hmass : 0 < ∑ i ∈ s, volume (V i).shade :=
    ambient_shade_mass_pos_of_hereditary_fullness hdelta0 hdelta1 V
      hs2s hs2ne (p.η 0) hhered
  have hparent : IsParentFamily s (fun i => (V i).toTube)
      s (fun i => (V i).toTube) id :=
    isParentFamily_self_of_pairwiseEssentiallyDistinct hdelta0 hdelta1 V hED
  exact exists_firstSelected_fullAmbient_w51 hdim hdelta0 le_rfl hdelta1
    V (fun i => (V i).toTube) id hball hparent hmass

#print axioms exists_firstSelected_fullAmbient_w51
#print axioms exists_caseTwo_fullAmbient_endpoint_firstSelected_w51

end
end Kakeya.ml1Boot.W51FullAmbientFirst
end
