import MyLeanRepo.Kakeya.Cinematic.Section5.Counting
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData

/-!
# Representative good pairs in the metric-automatic regime

When the representative metric threshold is strictly below the original
finite-family separation scale, every off-diagonal pair in a retained fiber
passes the metric condition. The diagonal is the only metric-bad point in
each row. Tangency bad pairs are still controlled by the second two-ends
nonconcentration estimate.
-/

namespace Kakeya.Cinematic

lemma representative_metric_automatic_good_pairs
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (hdelta : 0 < delta)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (p : E)
    (metricLower tangencyCut : ℝ)
    (hmetricAuto : metricLower < data.separationScale)
    (htangencyCut : 0 < tangencyCut)
    (htangencyCut_one : tangencyCut < 1)
    (htangencyScale :
      delta / data.exactDelta p < tangencyCut)
    (htangencySmall :
      6 * Real.rpow tangencyCut eta ≤ 1)
    (hcard : 2 ≤ (data.assignment.fiber p).card) :
    let G := data.assignment.fiber p
    let goodPairs :=
      (G.toFinset.product G.toFinset).filter fun pair =>
        metricLower < c2Distance pair.2 pair.1 ∧
          tangencyCut * DeltaRep / 2 ≤
            tangencyParameterOn data.interval pair.2 pair.1 + delta
    G.card ^ 2 ≤ 3 * goodPairs.card := by
  classical
  let G := data.assignment.fiber p
  let S := G.toFinset
  let badMetric : C2Function → Finset C2Function := fun g => {g}
  let badTangency : C2Function → Finset C2Function := fun g =>
    S.filter fun f =>
      tangencyParameterOn data.interval f g + delta <
        tangencyCut * data.exactDelta p
  have hS_coe : (S : Set C2Function) = G.carrier := by
    simp [S, G, FiniteFunctionFamily.toFinset]
  have hG_card : G.card = S.card := by
    have h1 : G.card = G.carrier.ncard := rfl
    have h2 : (S : Set C2Function).ncard = S.card :=
      Set.ncard_coe_finset S
    rw [h1, ← hS_coe, h2]
  have hbadMetric :
      ∀ g ∈ S, (S ∩ badMetric g).card ≤ 1 := by
    intro g _hg
    have hsub : S ∩ badMetric g ⊆ ({g} : Finset C2Function) := by
      simpa [badMetric] using
        (Finset.inter_subset_right : S ∩ ({g} : Finset C2Function) ⊆ {g})
    exact (Finset.card_le_card hsub).trans (by simp)
  have hbadTangency :
      ∀ g ∈ S, 3 * (S ∩ badTangency g).card ≤ S.card := by
    intro g hg
    have hgG : g ∈ G.carrier := by
      rw [← hS_coe]
      exact hg
    have hgMetric :
        g ∈ (data.metricFiber p).carrier :=
      data.fiber_subset_metric p hgG
    let A : Set C2Function :=
      (data.metricFiber p).carrier ∩
        {f | tangencyParameterOn data.interval f g ≤
          tangencyCut * data.exactDelta p}
    have hbad_sub : ((badTangency g : Finset C2Function) : Set C2Function) ⊆ A := by
      intro f hf
      have hf' : f ∈ S ∧
          tangencyParameterOn data.interval f g + delta <
            tangencyCut * data.exactDelta p := by
        simpa [badTangency] using hf
      have hfG : f ∈ G.carrier := by
        rw [← hS_coe]
        exact hf'.1
      refine ⟨data.fiber_subset_metric p hfG, ?_⟩
      have hlt :
          tangencyParameterOn data.interval f g <
            tangencyParameterOn data.interval f g + delta :=
        lt_add_of_pos_right _ hdelta
      exact (hlt.trans hf'.2).le
    have hA_finite : A.Finite :=
      (data.metricFiber p).finite.subset Set.inter_subset_left
    have hcard_le :
        (badTangency g).card ≤ A.ncard := by
      have h :=
        Set.ncard_le_ncard hbad_sub hA_finite
      simpa using h
    have hraw :
        (A.ncard : ℝ) ≤
          2 * Real.rpow tangencyCut eta *
            ((data.tangencyFiber p).card : ℝ) := by
      simpa [A] using
        (data.certificate p).tangency_nonconcentration
          g hgMetric tangencyCut htangencyScale htangencyCut_one
    have hbad_real :
        ((badTangency g).card : ℝ) ≤
          2 * Real.rpow tangencyCut eta * (G.card : ℝ) := by
      have hcard_real :
          ((badTangency g).card : ℝ) ≤ (A.ncard : ℝ) := by
        exact_mod_cast hcard_le
      have hTG : data.tangencyFiber p = G := by
        exact (data.assignment_fiber p).symm
      rw [hTG] at hraw
      exact hcard_real.trans hraw
    have hG_nonneg : 0 ≤ (G.card : ℝ) := by positivity
    have hscaled :
        3 * ((badTangency g).card : ℝ) ≤ (G.card : ℝ) := by
      calc
        3 * ((badTangency g).card : ℝ) ≤
            3 * (2 * Real.rpow tangencyCut eta * (G.card : ℝ)) := by
          gcongr
        _ = (6 * Real.rpow tangencyCut eta) * (G.card : ℝ) := by ring
        _ ≤ 1 * (G.card : ℝ) :=
          mul_le_mul_of_nonneg_right htangencySmall hG_nonneg
        _ = (G.card : ℝ) := one_mul _
    have hinter : S ∩ badTangency g = badTangency g := by
      apply Finset.inter_eq_right.mpr
      exact Finset.filter_subset _ _
    rw [hinter]
    have hscaled_nat :
        3 * (badTangency g).card ≤ G.card := by
      exact_mod_cast hscaled
    simpa [hG_card] using hscaled_nat
  have hcount :
      S.card ^ 2 ≤
        3 * ((S.product S).filter fun pair =>
          pair.2 ∉ badMetric pair.1 ∧
            pair.2 ∉ badTangency pair.1).card :=
    good_pair_counting_one_diagonal
      C2Function S badMetric badTangency
      (by
        rw [← hG_card]
        simpa [G] using hcard)
      hbadMetric hbadTangency
  let automaticPairs :=
    (S.product S).filter fun pair =>
      pair.2 ∉ badMetric pair.1 ∧
        pair.2 ∉ badTangency pair.1
  let goodPairs :=
    (G.toFinset.product G.toFinset).filter fun pair =>
      metricLower < c2Distance pair.2 pair.1 ∧
        tangencyCut * DeltaRep / 2 ≤
          tangencyParameterOn data.interval pair.2 pair.1 + delta
  have hmetric :
      ∀ pair ∈ automaticPairs,
        metricLower < c2Distance pair.2 pair.1 := by
    intro pair hpair
    have hmem : pair.1 ∈ S ∧ pair.2 ∈ S :=
      Finset.mem_product.mp (Finset.mem_filter.mp hpair).1
    have hnotDiagonal :
        pair.2 ≠ pair.1 := by
      have hnot := (Finset.mem_filter.mp hpair).2.1
      simpa [badMetric] using hnot
    have hsep :=
      data.fiber_separated p
        (f := pair.2) (g := pair.1) (by
          rw [← hS_coe]
          exact hmem.2)
        (by
          rw [← hS_coe]
          exact hmem.1)
        hnotDiagonal
    exact hmetricAuto.trans_le hsep
  have htangency :
      ∀ pair ∈ automaticPairs,
        tangencyCut * DeltaRep / 2 ≤
          tangencyParameterOn data.interval pair.2 pair.1 + delta := by
    intro pair hpair
    have hnot := (Finset.mem_filter.mp hpair).2.2
    have hexact :
        tangencyCut * data.exactDelta p ≤
          tangencyParameterOn data.interval pair.2 pair.1 + delta := by
      exact not_lt.mp (by
        intro hlt
        apply hnot
        have hmem : pair.2 ∈ S :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).2
        exact Finset.mem_filter.mpr ⟨hmem, hlt⟩)
    have hrep :
        tangencyCut * DeltaRep / 2 ≤
          tangencyCut * data.exactDelta p := by
      have h :=
        data.repDelta_le_two_exactDelta p
      have hscaled :=
        mul_le_mul_of_nonneg_left h htangencyCut.le
      linarith
    exact hrep.trans hexact
  have hsubset : automaticPairs ⊆ goodPairs := by
    intro pair hpair
    have hmem := (Finset.mem_filter.mp hpair).1
    exact Finset.mem_filter.mpr
      ⟨by simpa [S, G] using hmem,
        hmetric pair hpair, htangency pair hpair⟩
  have hcards :
      automaticPairs.card ≤ goodPairs.card :=
    Finset.card_le_card hsubset
  have hcount' :
      S.card ^ 2 ≤ 3 * automaticPairs.card := by
    simpa [automaticPairs] using hcount
  have hfinal :
      S.card ^ 2 ≤ 3 * goodPairs.card :=
    hcount'.trans (mul_le_mul_of_nonneg_left hcards (by norm_num))
  simpa [G, S, goodPairs, hG_card] using hfinal

end Kakeya.Cinematic
