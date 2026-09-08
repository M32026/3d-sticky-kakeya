module

public import Kakeya.DimensionThree.MainLemma1.ModuleSafeMiddleProducerW54
public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamSameWitnessW50
public import Kakeya.DimensionThree.MainLemma1.OneScaleNoUnif
public import Kakeya.DimensionThree.MainLemma1.FixedTreeRegularize
public import Kakeya.DimensionThree.MainLemma1.WZGlobalCrossing
public import Kakeya.DimensionThree.MainLemma1.WZCanonicalQBand
public import Kakeya.DimensionThree.MainLemma1.BallPort
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius
public import Kakeya.DimensionThree.MainLemma1.CapacityLedger
public import Kakeya.DimensionThree.MainLemma1.TwoLoads
public import Kakeya.ConvexBody.ContainerChange
public import Mathlib.Order.Filter.Finite

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube
open scoped NNReal ENNReal

namespace Kakeya.WangZahl

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

theorem nodeAncestor_trans
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {a b c : Nat} (hab : a <= b) (hbc : b <= c) (hc : c <= N)
    {w : iota} (hw : w ∈ U.cover.indexSet c) :
    U.nodeAncestor b a (U.nodeAncestor c b w) = U.nodeAncestor c a w := by
  have hb : b <= N := hbc.trans hc
  obtain ⟨i, hi, hwi, hcbi⟩ :=
    U.exists_nodeAncestor_witness (a := b) hc hs hw
  have hbai := nodeAncestor_assign_eq U hs hab hb hi
  have hcai := nodeAncestor_assign_eq U hs (hab.trans hbc) hc hi
  rw [hwi] at hcai
  rw [hcbi, hbai]
  exact hcai.symm

theorem activeRhoParents_eq_singleton_of_constant_ancestor
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) {b a : Nat}
    {tauNodes : Finset iota} (htauNonempty : tauNodes.Nonempty) {p : iota}
    (hconstant : forall w, w ∈ tauNodes -> U.nodeAncestor b a w = p) :
    activeRhoParents U b a tauNodes = {p} := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hq
    have hwp := hconstant w hw
    simpa [← hwq, hwp]
  · intro q hq
    have hqp : q = p := Finset.mem_singleton.mp hq
    obtain ⟨w, hw⟩ := htauNonempty
    subst q
    exact Finset.mem_image.mpr ⟨w, hw, hconstant w hw⟩

theorem tauAncestorClass_eq_of_constant_ancestor
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) {b a : Nat}
    {tauNodes : Finset iota} {p : iota}
    (hconstant : forall w, w ∈ tauNodes -> U.nodeAncestor b a w = p) :
    tauAncestorClass U b a tauNodes p = tauNodes := by
  classical
  ext w
  constructor
  · intro hw
    exact (mem_tauAncestorClass U b a tauNodes p w).mp hw |>.1
  · intro hw
    exact (mem_tauAncestorClass U b a tauNodes p w).mpr ⟨hw, hconstant w hw⟩

theorem oldCanonicalFibre_eq_stoppingCore
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {a sigma b : Nat} (ha : a <= sigma) (hsigma : sigma <= b) (hb : b <= N)
    {tauNodes source : Finset iota} (htau : tauNodes ⊆ U.cover.indexSet b)
    {pSigma : iota}
    (hsource : source = tauAncestorClass U b sigma tauNodes pSigma) :
    let pStop := U.nodeAncestor sigma a pSigma
    tauAncestorClass U b a source pStop = source := by
  classical
  dsimp only
  apply tauAncestorClass_eq_of_constant_ancestor U
  intro w hw
  have hwSource : w ∈ tauAncestorClass U b sigma tauNodes pSigma := by
    rwa [← hsource]
  have hwData := (mem_tauAncestorClass U b sigma tauNodes pSigma w).mp hwSource
  have htrans := nodeAncestor_trans U hs ha hsigma hb (htau hwData.1)
  rw [hwData.2] at htrans
  exact htrans.symm

end

end Kakeya.WangZahl

namespace Kakeya.ml1Boot

noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
theorem multiplicity_pos_of_sum_shade_pos {iota : Type*} {delta : NNReal}
    {s : Finset iota} {V : iota -> ShadedTube delta E}
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade) :
    0 < ShadedBody.multiplicity s (fun i => (V i).toShadedBody) := by
  have hnotzero : ¬ ∀ i ∈ s, volume (V i).shade = 0 := by
    intro hzero
    have hsumzero : (∑ i ∈ s, volume (V i).shade) = 0 :=
      Finset.sum_eq_zero fun i hi => hzero i hi
    rw [hsumzero] at hmass
    exact (lt_irrefl 0) hmass
  exact lt_of_lt_of_le zero_lt_one
    (ShadedBody.one_le_multiplicity s (fun i => (V i).toShadedBody) hnotzero)

theorem b3_raw_nodes_carry_leaf {iota : Type u} {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet sPrime T N C) {b : Nat} (hb : b <= N)
    (hsPrime : sPrime.Nonempty) :
    forall k, k ∈ U.cover.indexSet b ->
      exists i, i ∈ sPrime /\ U.cover.assign b i = k := by
  intro k hk
  obtain ⟨i, hi⟩ := MultiScaleFac.coverClass_nonempty_of_mem_parent U hb hsPrime hk
  have hi' : i ∈ sPrime /\ U.cover.assign b i = k := by
    simpa [Tube.coverClass] using hi
  exact ⟨i, hi'.1, hi'.2⟩

theorem exists_maxMultiplicity_tauAncestorClass_w48
    {iota : Type*}
    {delta : NNReal} {s : Finset iota} {T : iota -> Tube delta E}
    {N : Nat} {C : NNReal} (U : Tube.UniformTubeSet s T N C)
    {b a : Nat} {nodes : Finset iota} (hnodes : nodes.Nonempty)
    (Z : iota -> ShadedBody E) :
    ∃ p ∈ Kakeya.WangZahl.activeRhoParents U b a nodes,
      (Kakeya.WangZahl.tauAncestorClass U b a nodes p).Nonempty /\
      ShadedBody.multiplicity nodes Z <=
        ((Kakeya.WangZahl.activeRhoParents U b a nodes).card : ENNReal) *
          ShadedBody.multiplicity
            (Kakeya.WangZahl.tauAncestorClass U b a nodes p) Z := by
  classical
  let parents := Kakeya.WangZahl.activeRhoParents U b a nodes
  let cls : iota -> Finset iota :=
    fun p => Kakeya.WangZahl.tauAncestorClass U b a nodes p
  have hparents : parents.Nonempty := by
    simpa [parents, Kakeya.WangZahl.activeRhoParents] using
      hnodes.image (U.nodeAncestor b a)
  obtain ⟨p, hp, hpmax⟩ := Finset.exists_max_image parents
    (fun q => ShadedBody.multiplicity (cls q) Z) hparents
  have hmaps : forall k, k ∈ nodes -> U.nodeAncestor b a k ∈ parents := by
    intro k hk
    exact Finset.mem_image_of_mem _ hk
  have hsplit := multiplicity_le_sum_fiberwise nodes Z parents
    (U.nodeAncestor b a) hmaps
  have hfibre : forall q, fibre nodes (U.nodeAncestor b a) q = cls q := by
    intro q
    ext k
    simp [fibre, cls, Kakeya.WangZahl.mem_tauAncestorClass]
  refine ⟨p, hp, ?_, ?_⟩
  · exact Kakeya.WangZahl.tauAncestorClass_nonempty U b a nodes hp
  · calc
      ShadedBody.multiplicity nodes Z <=
          ∑ q ∈ parents,
            ShadedBody.multiplicity (fibre nodes (U.nodeAncestor b a) q) Z := hsplit
      _ = ∑ q ∈ parents, ShadedBody.multiplicity (cls q) Z := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [hfibre q]
      _ <= ∑ _q ∈ parents, ShadedBody.multiplicity (cls p) Z := by
        exact Finset.sum_le_sum fun q hq => hpmax q hq
      _ = (parents.card : ENNReal) * ShadedBody.multiplicity (cls p) Z := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Kakeya.WangZahl.activeRhoParents U b a nodes).card : ENNReal) *
          ShadedBody.multiplicity
            (Kakeya.WangZahl.tauAncestorClass U b a nodes p) Z := by
        rfl

theorem exists_positive_maxMultiplicity_tauAncestorClass_w48
    {iota : Type*} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C)
    {b a : Nat} {nodes : Finset iota}
    {Z : iota -> ShadedTube (Tube.gridScale delta N b) E}
    (hnodes : nodes.Nonempty)
    (hmass : 0 < ∑ k ∈ nodes, volume (Z k).shade) :
    ∃ p ∈ Kakeya.WangZahl.activeRhoParents U b a nodes,
      (Kakeya.WangZahl.tauAncestorClass U b a nodes p).Nonempty /\
      0 < ∑ k ∈ Kakeya.WangZahl.tauAncestorClass U b a nodes p,
        volume (Z k).shade /\
      ShadedBody.multiplicity nodes (fun k => (Z k).toShadedBody) <=
        ((Kakeya.WangZahl.activeRhoParents U b a nodes).card : ENNReal) *
          ShadedBody.multiplicity
            (Kakeya.WangZahl.tauAncestorClass U b a nodes p)
            (fun k => (Z k).toShadedBody) := by
  classical
  obtain ⟨p, hp, hcoreNe, hbridge⟩ :=
    exists_maxMultiplicity_tauAncestorClass_w48 U hnodes
      (fun k => (Z k).toShadedBody)
  have hnodesMul : 0 < ShadedBody.multiplicity nodes
      (fun k => (Z k).toShadedBody) := multiplicity_pos_of_sum_shade_pos hmass
  have hcoreMul : 0 < ShadedBody.multiplicity
      (Kakeya.WangZahl.tauAncestorClass U b a nodes p)
      (fun k => (Z k).toShadedBody) := by
    by_contra hnot
    have hz : ShadedBody.multiplicity
        (Kakeya.WangZahl.tauAncestorClass U b a nodes p)
        (fun k => (Z k).toShadedBody) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hz, mul_zero] at hbridge
    exact (not_le_of_gt hnodesMul) hbridge
  have hcoreMass : 0 < ∑ k ∈ Kakeya.WangZahl.tauAncestorClass U b a nodes p,
      volume (Z k).shade := by
    by_contra hnot
    have hz : (∑ k ∈ Kakeya.WangZahl.tauAncestorClass U b a nodes p,
        volume (Z k).shade) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [ShadedBody.multiplicity_eq_div, hz, ENNReal.zero_div] at hcoreMul
    exact (lt_irrefl 0) hcoreMul
  exact ⟨p, hp, hcoreNe, hcoreMass, hbridge⟩

theorem eventually_endpoint_exact_q0_lower_w47
    {eta : Real} (heta : 0 < eta) {A : ENNReal} (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) :
    ∀ᶠ (d : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall {q : NNReal}, d <= q -> q <= 1 ->
        (d : ENNReal) ^ (2 * eta) <=
          (A * (d : ENNReal) ^ (-(eta / 4)))⁻¹ * (q : ENNReal) ^ eta := by
  have ha : 0 < eta / 4 := by positivity
  have hAinv : 0 < A⁻¹ := by
    rw [ENNReal.inv_pos]
    exact hAtop
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos ha hAinv,
      self_mem_nhdsWithin]
    with d hAabs hd0
  intro q hdq hq1
  have hdE0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd0.ne'
  have hdE1 : (d : ENNReal) <= 1 := by exact_mod_cast hdq.trans hq1
  have hqpow : (d : ENNReal) ^ eta <= (q : ENNReal) ^ eta := by
    exact ENNReal.rpow_le_rpow (by exact_mod_cast hdq) heta.le
  have hcoef : (d : ENNReal) ^ (eta / 2) <=
      (A * (d : ENNReal) ^ (-(eta / 4)))⁻¹ := by
    calc
      (d : ENNReal) ^ (eta / 2) =
          (d : ENNReal) ^ (eta / 4) * (d : ENNReal) ^ (eta / 4) := by
        rw [← ENNReal.rpow_add _ _ hdE0 ENNReal.coe_ne_top]
        congr 1
        ring
      _ <= A⁻¹ * (d : ENNReal) ^ (eta / 4) := by gcongr
      _ = (A * (d : ENNReal) ^ (-(eta / 4)))⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAtop), ENNReal.rpow_neg]
        simp only [inv_inv]
  calc
    (d : ENNReal) ^ (2 * eta) <=
        (d : ENNReal) ^ (eta / 2 + eta) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
    _ = (d : ENNReal) ^ (eta / 2) * (d : ENNReal) ^ eta := by
      rw [ENNReal.rpow_add _ _ hdE0 ENNReal.coe_ne_top]
    _ <= (A * (d : ENNReal) ^ (-(eta / 4)))⁻¹ *
        (q : ENNReal) ^ eta := by gcongr

end


end Kakeya.ml1Boot

namespace Kakeya.ml1Boot.W48ReverseQBand

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

theorem exists_firstCrossing_of_crossing
    {Crosses : Nat -> Prop} {sigma : Nat} (hSigma : Crosses sigma) :
    exists a, a <= sigma /\ Crosses a /\
      (a = 0 ∨ (0 < a /\ ¬ Crosses (a - 1))) := by
  classical
  have hex : exists a, Crosses a := ⟨sigma, hSigma⟩
  let a := Nat.find hex
  have ha : Crosses a := Nat.find_spec hex
  have haSigma : a <= sigma := Nat.find_le hSigma
  refine ⟨a, haSigma, ha, ?_⟩
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · exact Or.inl ha0
  · exact Or.inr ⟨ha0, Nat.find_min hex (Nat.sub_lt ha0 Nat.one_pos)⟩

theorem hierarchyGlobalCrossing_of_normalizedQ_lower_singleParent
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hdelta : 0 < delta)
    {b a : Nat} {nodes : Finset iota} (hnodes : nodes.Nonempty) {p : iota}
    (hconstant : forall w, w ∈ nodes -> U.nodeAncestor b a w = p)
    {Qret : ENNReal} (hQretTop : Qret ≠ ⊤)
    (hQret : Qret <=
      ((((Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 * nodes.card :
        NNReal) : ENNReal))) :
    Kakeya.WangZahl.hierarchyGlobalCrossing U b nodes Qret.toNNReal a := by
  have hQretNN : Qret.toNNReal <=
      (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 * nodes.card := by
    rw [← ENNReal.coe_le_coe]
    simpa [ENNReal.coe_toNNReal hQretTop] using hQret
  have hactive :=
    Kakeya.WangZahl.activeRhoParents_eq_singleton_of_constant_ancestor
      U hnodes hconstant
  have hrho0 : Tube.gridScale delta N a ≠ 0 :=
    (Tube.gridScale_pos hdelta N a).ne'
  unfold Kakeya.WangZahl.hierarchyGlobalCrossing Kakeya.WangZahl.GlobalCrossing
  rw [hactive]
  simp only [Finset.card_singleton, Nat.cast_one, mul_one]
  calc
    Qret.toNNReal * Tube.gridScale delta N a ^ 2 <=
        ((Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 * nodes.card) *
          Tube.gridScale delta N a ^ 2 := by gcongr
    _ = Tube.gridScale delta N b ^ 2 * nodes.card := by
      field_simp [hrho0]

theorem normalizedQ_lower_of_singleParent_crossing
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C theta : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hdelta : 0 < delta)
    {b a : Nat} {nodes : Finset iota} (hnodes : nodes.Nonempty) {p : iota}
    (hconstant : forall w, w ∈ nodes -> U.nodeAncestor b a w = p)
    (hcross : Kakeya.WangZahl.hierarchyGlobalCrossing U b nodes theta a) :
    theta <= (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
      ((Kakeya.WangZahl.tauAncestorClass U b a nodes p).card : NNReal) := by
  have hactive :=
    Kakeya.WangZahl.activeRhoParents_eq_singleton_of_constant_ancestor
      U hnodes hconstant
  have hcore :=
    Kakeya.WangZahl.tauAncestorClass_eq_of_constant_ancestor U hconstant
  unfold Kakeya.WangZahl.hierarchyGlobalCrossing Kakeya.WangZahl.GlobalCrossing at hcross
  rw [hactive] at hcross
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hcross
  rw [hcore]
  rw [show (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
      (nodes.card : NNReal) =
      (Tube.gridScale delta N b ^ 2 * (nodes.card : NNReal)) /
        Tube.gridScale delta N a ^ 2 by field_simp]
  exact (le_div_iff₀ (pow_pos (Tube.gridScale_pos hdelta N a) 2)).mpr hcross

theorem normalizedQ_upper_of_predecessor_failure_singleParent
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C theta : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hdelta : 0 < delta)
    {b a : Nat} {nodes : Finset iota} (hnodes : nodes.Nonempty) {pPrev : iota}
    (hconstantPrev : forall w, w ∈ nodes -> U.nodeAncestor b (a - 1) w = pPrev)
    (hfail : ¬ Kakeya.WangZahl.hierarchyGlobalCrossing U b nodes theta (a - 1)) :
    (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 * nodes.card <
      theta * (Tube.gridScale delta N (a - 1) / Tube.gridScale delta N a) ^ 2 := by
  have hactive :=
    Kakeya.WangZahl.activeRhoParents_eq_singleton_of_constant_ancestor
      U hnodes hconstantPrev
  unfold Kakeya.WangZahl.hierarchyGlobalCrossing Kakeya.WangZahl.GlobalCrossing at hfail
  rw [hactive] at hfail
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hfail
  have hstrict :
      Tube.gridScale delta N b ^ 2 * nodes.card <
        theta * Tube.gridScale delta N (a - 1) ^ 2 := lt_of_not_ge hfail
  have hrho0 : 0 < Tube.gridScale delta N a := Tube.gridScale_pos hdelta N a
  rw [show (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 * nodes.card =
      (Tube.gridScale delta N b ^ 2 * nodes.card) /
        Tube.gridScale delta N a ^ 2 by field_simp]
  rw [show theta * (Tube.gridScale delta N (a - 1) /
      Tube.gridScale delta N a) ^ 2 =
      (theta * Tube.gridScale delta N (a - 1) ^ 2) /
        Tube.gridScale delta N a ^ 2 by field_simp]
  exact div_lt_div_of_pos_right hstrict (pow_pos hrho0 2)

theorem exists_firstProtectedCrossing_with_exact_normalizedQ_lower
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hdelta : 0 < delta) (hs : s.Nonempty)
    {b sigma : Nat} (hsigma : sigma <= b) (hb : b <= N)
    {tauNodes source : Finset iota} (htau : tauNodes <= U.cover.indexSet b)
    (hsourceNe : source.Nonempty) {pSigma : iota}
    (hsource : source = Kakeya.WangZahl.tauAncestorClass U b sigma tauNodes pSigma)
    {Qret : ENNReal} (hQretTop : Qret ≠ ⊤)
    (hQret : Qret <=
      ((((Tube.gridScale delta N b / Tube.gridScale delta N sigma) ^ 2 * source.card :
        NNReal) : ENNReal))) :
    exists a p,
      a <= sigma /\
      Kakeya.WangZahl.hierarchyGlobalCrossing U b source Qret.toNNReal a /\
      (a = 0 ∨ (0 < a /\
        ¬ Kakeya.WangZahl.hierarchyGlobalCrossing U b source Qret.toNNReal (a - 1))) /\
      p = U.nodeAncestor sigma a pSigma /\
      Kakeya.WangZahl.tauAncestorClass U b a source p = source /\
      Qret <= ((((Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
        (Kakeya.WangZahl.tauAncestorClass U b a source p).card : NNReal) : ENNReal)) := by
  have hconstantSigma : forall w, w ∈ source -> U.nodeAncestor b sigma w = pSigma := by
    intro w hw
    have hw' : w ∈ Kakeya.WangZahl.tauAncestorClass U b sigma tauNodes pSigma := by
      rwa [← hsource]
    exact (Kakeya.WangZahl.mem_tauAncestorClass U b sigma tauNodes pSigma w).mp hw' |>.2
  have hcrossSigma := hierarchyGlobalCrossing_of_normalizedQ_lower_singleParent
    U hdelta hsourceNe hconstantSigma hQretTop hQret
  obtain ⟨a, haSigma, hcross, hfirst⟩ :=
    exists_firstCrossing_of_crossing (Crosses := fun j =>
      Kakeya.WangZahl.hierarchyGlobalCrossing U b source Qret.toNNReal j) hcrossSigma
  let p := U.nodeAncestor sigma a pSigma
  have hcore : Kakeya.WangZahl.tauAncestorClass U b a source p = source := by
    exact Kakeya.WangZahl.oldCanonicalFibre_eq_stoppingCore
      U hs haSigma hsigma hb htau hsource
  have hconstant : forall w, w ∈ source -> U.nodeAncestor b a w = p := by
    intro w hw
    have hwCore : w ∈ Kakeya.WangZahl.tauAncestorClass U b a source p := by
      rwa [hcore]
    exact (Kakeya.WangZahl.mem_tauAncestorClass U b a source p w).mp hwCore |>.2
  have hlowerNN := normalizedQ_lower_of_singleParent_crossing
    U hdelta hsourceNe hconstant hcross
  have hlower : Qret <=
      ((((Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
        (Kakeya.WangZahl.tauAncestorClass U b a source p).card : NNReal) : ENNReal)) := by
    rw [← ENNReal.coe_toNNReal hQretTop]
    exact_mod_cast hlowerNN
  exact ⟨a, p, haSigma, hcross, hfirst, rfl, hcore, hlower⟩

theorem exists_firstProtectedCrossing_with_exact_QBand_or_top
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hdelta : 0 < delta) (hs : s.Nonempty)
    {b sigma : Nat} (hsigma : sigma <= b) (hb : b <= N)
    {tauNodes source : Finset iota} (htau : tauNodes <= U.cover.indexSet b)
    (hsourceNe : source.Nonempty) {pSigma : iota}
    (hsource : source = Kakeya.WangZahl.tauAncestorClass U b sigma tauNodes pSigma)
    {Qret : ENNReal} (hQretTop : Qret ≠ ⊤)
    (hQret : Qret <=
      ((((Tube.gridScale delta N b / Tube.gridScale delta N sigma) ^ 2 * source.card :
        NNReal) : ENNReal))) :
    exists a p,
      a <= sigma /\
      Kakeya.WangZahl.hierarchyGlobalCrossing U b source Qret.toNNReal a /\
      p = U.nodeAncestor sigma a pSigma /\
      Kakeya.WangZahl.tauAncestorClass U b a source p = source /\
      Qret <= ((
        (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
          (Kakeya.WangZahl.tauAncestorClass U b a source p).card : NNReal) : ENNReal) /\
      (a = 0 ∨
        ((
          (Tube.gridScale delta N b / Tube.gridScale delta N a) ^ 2 *
            (Kakeya.WangZahl.tauAncestorClass U b a source p).card : NNReal) : ENNReal) <
          Qret * ((
            (Tube.gridScale delta N (a - 1) / Tube.gridScale delta N a) ^ 2 :
              NNReal) : ENNReal)) := by
  obtain ⟨a, p, haSigma, hcross, hfirst, hp, hcore, hlower⟩ :=
    exists_firstProtectedCrossing_with_exact_normalizedQ_lower
      U hdelta hs hsigma hb htau hsourceNe hsource hQretTop hQret
  refine ⟨a, p, haSigma, hcross, hp, hcore, hlower, ?_⟩
  rcases hfirst with ha0 | ⟨ha0, hfail⟩
  · exact Or.inl ha0
  · right
    have hcorePrev := Kakeya.WangZahl.oldCanonicalFibre_eq_stoppingCore
      U hs ((Nat.sub_le a 1).trans haSigma) hsigma hb htau hsource
    let pPrev := U.nodeAncestor sigma (a - 1) pSigma
    have hconstantPrev : forall w, w ∈ source ->
        U.nodeAncestor b (a - 1) w = pPrev := by
      intro w hw
      have hwCore : w ∈ Kakeya.WangZahl.tauAncestorClass U b (a - 1) source pPrev := by
        rwa [hcorePrev]
      exact (Kakeya.WangZahl.mem_tauAncestorClass U b (a - 1) source pPrev w).mp hwCore |>.2
    have huppNN := normalizedQ_upper_of_predecessor_failure_singleParent
      U hdelta hsourceNe hconstantPrev hfail
    rw [hcore]
    rw [← ENNReal.coe_toNNReal hQretTop]
    exact_mod_cast huppNN

theorem adjacentGridRatio_sq_eq_scaleGapLoss_two
    {delta : NNReal} (hdelta : 0 < delta) {a : Nat} (ha : 0 < a) :
    ((((Tube.gridScale delta (Tube.ssfGridLen delta) (a - 1) /
          Tube.gridScale delta (Tube.ssfGridLen delta) a) ^ 2 : NNReal) : ENNReal)) =
      ENNReal.ofReal (StickyKakeya.scaleGapLoss 2 delta) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [Tube.gridScale_div_gridScale hdelta, NNReal.coe_pow, NNReal.coe_rpow]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  unfold StickyKakeya.scaleGapLoss
  congr 1
  rw [Nat.cast_sub (by omega : 1 <= a)]
  push_cast
  ring

theorem eventually_adjacentGridRatio_sq_le_six_eta
    {eta : Real} (heta : 0 < eta) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall a : Nat, 0 < a ->
        ((((Tube.gridScale delta (Tube.ssfGridLen delta) (a - 1) /
            Tube.gridScale delta (Tube.ssfGridLen delta) a) ^ 2 : NNReal) : ENNReal)) <=
          (delta : ENNReal) ^ (-(6 * eta)) := by
  obtain ⟨delta0, hdelta0, _hdelta01, hgap⟩ :=
    StickyKakeya.exists_threshold_scaleGapLoss_le 2 (6 * eta) (by positivity)
  filter_upwards [Kakeya.ml1Boot.eventually_le_nhdsGT (c := delta0) hdelta0,
      self_mem_nhdsWithin]
    with delta hdeltale hdelta
  intro a ha
  rw [adjacentGridRatio_sq_eq_scaleGapLoss_two hdelta ha]
  have hdeltaR : 0 < (delta : Real) := by exact_mod_cast hdelta
  have hgapReal := hgap hdelta hdeltale
  have hcast := ENNReal.ofReal_le_ofReal hgapReal
  rw [← ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_rpow_of_pos hdeltaR]
  simpa using hcast

theorem qmin_mul_adjacent_sq_le_symmetric_upper
    {delta : NNReal} (hdelta : 0 < delta) {eta : Real}
    {adj : ENNReal} (hadj : adj <= (delta : ENNReal) ^ (-(6 * eta))) :
    (delta : ENNReal) ^ (3 * eta) * adj <=
      (delta : ENNReal) ^ (-(3 * eta)) := by
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  calc
    (delta : ENNReal) ^ (3 * eta) * adj <=
        (delta : ENNReal) ^ (3 * eta) *
          (delta : ENNReal) ^ (-(6 * eta)) := by gcongr
    _ = (delta : ENNReal) ^ (3 * eta + -(6 * eta)) := by
      rw [ENNReal.rpow_add _ _ hdeltaE0 ENNReal.coe_ne_top]
    _ = (delta : ENNReal) ^ (-(3 * eta)) := by congr 1; ring

theorem eventually_exists_firstProtectedCrossing_with_symmetric_QBand_or_top
    {eta : Real} (heta : 0 < eta) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall {iota : Type u} {s : Finset iota}
        {T : iota -> Tube delta E} {C : NNReal}
        (U : Tube.UniformTubeSet s T (Tube.ssfGridLen delta) C),
        s.Nonempty ->
        forall {b sigma : Nat}, sigma <= b -> b <= Tube.ssfGridLen delta ->
        forall {tauNodes source : Finset iota},
        tauNodes <= U.cover.indexSet b -> source.Nonempty ->
        forall {pSigma : iota},
        source = Kakeya.WangZahl.tauAncestorClass U b sigma tauNodes pSigma ->
        (delta : ENNReal) ^ (3 * eta) <=
          ((((Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) sigma) ^ 2 * source.card :
              NNReal) : ENNReal)) ->
        exists a p,
          a <= sigma /\
          Kakeya.WangZahl.hierarchyGlobalCrossing U b source
            ((delta : ENNReal) ^ (3 * eta)).toNNReal a /\
          p = U.nodeAncestor sigma a pSigma /\
          Kakeya.WangZahl.tauAncestorClass U b a source p = source /\
          ((1 : ENNReal)⁻¹ * (delta : ENNReal) ^ (3 * eta) <=
            ((((Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) a) ^ 2 *
                (Kakeya.WangZahl.tauAncestorClass U b a source p).card :
                  NNReal) : ENNReal))) /\
          ((a = 0 /\ Tube.gridScale delta (Tube.ssfGridLen delta) a = 1) ∨
            (0 < a /\
              ((((Tube.gridScale delta (Tube.ssfGridLen delta) b /
                Tube.gridScale delta (Tube.ssfGridLen delta) a) ^ 2 *
                  (Kakeya.WangZahl.tauAncestorClass U b a source p).card :
                    NNReal) : ENNReal)) <=
                (1 : ENNReal) * (delta : ENNReal) ^ (-(3 * eta)))) := by
  filter_upwards [eventually_adjacentGridRatio_sq_le_six_eta heta,
      self_mem_nhdsWithin]
    with delta hadj hdelta
  intro iota s T C U hs b sigma hsigma hb tauNodes source htau hsourceNe
    pSigma hsource hterminal
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hQminTop : (delta : ENNReal) ^ (3 * eta) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 ENNReal.coe_ne_top
  obtain ⟨a, p, haSigma, hcross, hp, hcore, hlower, htopOrUpper⟩ :=
    exists_firstProtectedCrossing_with_exact_QBand_or_top
      U hdelta hs hsigma hb htau hsourceNe hsource hQminTop hterminal
  refine ⟨a, p, haSigma, hcross, hp, hcore, ?_, ?_⟩
  · simpa using hlower
  · rcases htopOrUpper with ha0 | hupper
    · exact Or.inl ⟨ha0, by simp [ha0]⟩
    · right
      have haPos : 0 < a := Nat.pos_of_ne_zero (by
        intro haZero
        have hlt := hupper
        have hle := hlower
        simp [haZero] at hlt hle
        exact (not_lt_of_ge hle) hlt)
      refine ⟨haPos, ?_⟩
      have hstep := hadj a haPos
      have habsorb := qmin_mul_adjacent_sq_le_symmetric_upper hdelta hstep
      simpa only [one_mul] using hupper.le.trans habsorb

end

end Kakeya.ml1Boot.W48ReverseQBand

namespace Kakeya.ml1Boot.W47EndpointLowCard

theorem normalizedQ_lower_of_capacity
    {A L q n CF : ENNReal} {eta : ℝ}
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hq0 : q ≠ 0) (hqtop : q ≠ ⊤)
    (hcap : 1 ≤ A * (q ^ 2 * n) * CF)
    (hCF : CF ≤ L * q ^ eta) :
    (A * L)⁻¹ * q ^ (-eta) ≤ q ^ 2 * n := by
  have hchain : 1 ≤ (A * L) * (q ^ 2 * n) * q ^ eta := by
    calc
      1 ≤ A * (q ^ 2 * n) * CF := hcap
      _ ≤ A * (q ^ 2 * n) * (L * q ^ eta) := by gcongr
      _ = (A * L) * (q ^ 2 * n) * q ^ eta := by ring
  have hAL0 : A * L ≠ 0 := mul_ne_zero hA0 hL0
  have hALtop : A * L ≠ ⊤ := ENNReal.mul_ne_top hAtop hLtop
  have hqeta0 : q ^ eta ≠ 0 := by
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with (⟨hzero, _⟩ | ⟨htop, _⟩)
    · exact hq0 hzero
    · exact hqtop htop
  have hqetatop : q ^ eta ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hq0 hqtop
  calc
    (A * L)⁻¹ * q ^ (-eta)
        ≤ (A * L)⁻¹ * q ^ (-eta) *
            ((A * L) * (q ^ 2 * n) * q ^ eta) := by
          simpa only [mul_one] using
            mul_le_mul_left' hchain ((A * L)⁻¹ * q ^ (-eta))
    _ = q ^ 2 * n := by
      rw [ENNReal.rpow_neg]
      calc
        (A * L)⁻¹ * (q ^ eta)⁻¹ * ((A * L) * (q ^ 2 * n) * q ^ eta) =
            ((A * L)⁻¹ * (A * L)) *
              (((q ^ eta)⁻¹ * q ^ eta) * (q ^ 2 * n)) := by ring
        _ = q ^ 2 * n := by
          rw [ENNReal.inv_mul_cancel hAL0 hALtop,
            ENNReal.inv_mul_cancel hqeta0 hqetatop]
          simp

/-- Capacity lower bound for the infimum-form Frostman constant.  The containment hypothesis is
the exact bridge needed to identify the anchor density with total family mass over anchor volume. -/
theorem one_le_capacity_mul_frostmanConstIn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {iota : Type*} {s : Finset iota} {W : iota → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {i0 : iota}
    (hi0 : i0 ∈ s) (hpos : volume (W i0).carrier ≠ 0)
    (hWK : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    {q : ENNReal} (hq : ∑ i ∈ s, volume (W i).carrier ≤ q * volume K.carrier) :
    1 ≤ q * frostmanConstIn s W K := by
  have hmax : 1 ≤ maxDensity s W :=
    Kakeya.ml1Ledger.one_le_maxDensity_of_mem hi0 hpos
  have hfr : ConvexSpaceBody.IsFrostmanIn s W K (frostmanConstIn s W K) := by
    simpa only [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant] using
      (ConvexSpaceBody.isFrostmanIn_frostmanConstant (s := s) (W := W) (K := K))
  have hmaxCF : maxDensity s W ≤ frostmanConstIn s W K * densityIn s W K :=
    hfr.maxDensity_le_of_carrier_subset hWK
  have hanchor : volume K.carrier ≤
      frostmanConstIn s W K * ∑ i ∈ s, volume (W i).carrier := by
    have hchain : 1 ≤
        (frostmanConstIn s W K * ∑ i ∈ s, volume (W i).carrier) /
          volume K.carrier := by
      calc
        1 ≤ maxDensity s W := hmax
        _ ≤ frostmanConstIn s W K * densityIn s W K := hmaxCF
        _ = (frostmanConstIn s W K * ∑ i ∈ s, volume (W i).carrier) /
              volume K.carrier := by
          rw [densityIn_of_all_le hWK, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop), one_mul] at hchain
  have hchain : 1 * volume K.carrier ≤
      (q * frostmanConstIn s W K) * volume K.carrier := by
    calc
      1 * volume K.carrier = volume K.carrier := one_mul _
      _ ≤ frostmanConstIn s W K * ∑ i ∈ s, volume (W i).carrier := hanchor
      _ ≤ frostmanConstIn s W K * (q * volume K.carrier) := by gcongr
      _ = (q * frostmanConstIn s W K) * volume K.carrier := by ring
  exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp hchain

/-- In dimension three, the relative volume capacity of a nonempty family of `tau`-tubes
inside a `theta`-tube is bounded by the normalized cardinality, up to the explicit tube-volume
constant.  No separation or distinctness hypothesis is used. -/
theorem one_le_tubeCapacity_mul_frostman
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {tau theta : NNReal} (htau0 : 0 < tau) (htau1 : tau ≤ 1) (htheta0 : 0 < theta)
    {iota : Type*} {s : Finset iota} (hs : s.Nonempty)
    (W : iota → Tube tau E) (K : Tube theta E)
    (hWK : ∀ i ∈ s, (W i).toConvexSpaceBody ≤ K.toConvexSpaceBody) :
    1 ≤
      (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
        (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal))) *
        frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K.toConvexSpaceBody := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  have hWlower : ∀ i,
      ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2 ≤
        volume (W i).carrier := by
    intro i
    simpa [hdim] using (W i).le_volume
  have hWpos : ∀ i, volume (W i).carrier ≠ 0 := by
    intro i
    apply ne_of_gt
    exact (ENNReal.mul_pos
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr htau0.ne'))).trans_le (hWlower i)
  have hmass : (∑ i ∈ s, volume (W i).carrier) ≠ 0 := by
    apply ne_of_gt
    exact (pos_iff_ne_zero.mpr (hWpos i0)).trans_le
      (Finset.single_le_sum (s := s) (f := fun i => volume (W i).carrier)
        (fun _ _ => bot_le) hi0)
  have hKlower :
      ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (theta : ENNReal) ^ 2 ≤
        volume K.carrier := by
    simpa [hdim] using K.le_volume
  have hK0 : volume K.carrier ≠ 0 := by
    apply ne_of_gt
    exact (ENNReal.mul_pos
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
      (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr htheta0.ne'))).trans_le hKlower
  have hKtop : volume K.carrier ≠ ⊤ := K.toConvexSpaceBody.isCompact.measure_ne_top
  have hsum :
      (∑ i ∈ s, volume (W i).carrier) ≤
        (s.card : ENNReal) *
          (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2) := by
    calc
      (∑ i ∈ s, volume (W i).carrier) ≤
          ∑ i ∈ s,
            (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2) := by
        exact Finset.sum_le_sum fun i _ => by simpa [hdim] using Tube.volume_le htau1 (W i)
      _ = (s.card : ENNReal) *
          (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcn0 : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have htheta_ne : theta ≠ 0 := htheta0.ne'
  have halgNN :
      (s.card : NNReal) * (Tube.volume_le.C 3 * tau ^ 2) =
        (Tube.volume_le.C 3 / Tube.le_volume.c 3) *
          ((tau / theta) ^ 2 * (s.card : NNReal)) *
          (Tube.le_volume.c 3 * theta ^ 2) := by
    field_simp
  have halg :
      (s.card : ENNReal) *
          (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2) =
        (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
          (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal))) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (theta : ENNReal) ^ 2) := by
    exact_mod_cast halgNN
  have hq :
      (∑ i ∈ s, volume (W i).carrier) ≤
        (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
          (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal))) *
          volume K.carrier := by
    calc
      (∑ i ∈ s, volume (W i).carrier) ≤
          (s.card : ENNReal) *
            (((Tube.volume_le.C 3 : NNReal) : ENNReal) * (tau : ENNReal) ^ 2) := hsum
      _ = (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
          (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal))) *
          (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (theta : ENNReal) ^ 2) := halg
      _ ≤ (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
          (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal))) *
          volume K.carrier := by gcongr
  exact one_le_capacity_mul_frostmanConstIn
    hi0 (hWpos i0) hWK hK0 hKtop hq

/-- The tube-capacity estimate combined with a relative Frostman upper bound. -/
theorem completeFibre_normalizedQ_lower_of_frostman
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {delta tau theta : NNReal} (hdelta0 : 0 < delta)
    (htau0 : 0 < tau) (htau1 : tau ≤ 1) (htheta0 : 0 < theta)
    {iota : Type*} {s : Finset iota} (hs : s.Nonempty)
    (W : iota → Tube tau E) (K : Tube theta E)
    (hWK : ∀ i ∈ s, (W i).toConvexSpaceBody ≤ K.toConvexSpaceBody) {eps eta : ℝ}
    (hCF : frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K.toConvexSpaceBody ≤
      (delta : ENNReal) ^ (-2 * eps) *
        (((theta / tau : NNReal) : ENNReal) ^ eta)) :
    ((((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-2 * eps))⁻¹ *
      (((tau / theta : NNReal) : ENNReal) ^ eta)) ≤
      (((tau / theta : NNReal) : ENNReal) ^ 2 * (s.card : ENNReal)) := by
  let A : ENNReal := ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal)
  let L : ENNReal := (delta : ENNReal) ^ (-2 * eps)
  let q : ENNReal := ((tau / theta : NNReal) : ENNReal)
  have hA0NN : Tube.volume_le.C 3 / Tube.le_volume.c 3 ≠ 0 :=
    div_ne_zero (Tube.volume_le.C_pos 3).ne' (Tube.le_volume.c_pos 3).ne'
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact ENNReal.coe_ne_zero.mpr hA0NN
  have hAtop : A ≠ ⊤ := by simp [A]
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hL0 : L ≠ 0 := by
    dsimp [L]
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with (⟨hzero, _⟩ | ⟨htop, _⟩)
    · exact hdeltaE0 hzero
    · exact hdeltaEtop htop
  have hLtop : L ≠ ⊤ := by
    dsimp [L]
    exact ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 hdeltaEtop
  have hq0NN : tau / theta ≠ 0 := (div_pos htau0 htheta0).ne'
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact ENNReal.coe_ne_zero.mpr hq0NN
  have hqtop : q ≠ ⊤ := by simp [q]
  have hinv : (((theta / tau : NNReal) : ENNReal) ^ eta) = q ^ (-eta) := by
    dsimp [q]
    rw [ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.coe_inv hq0NN, inv_div]
  have hcap :
      1 ≤ A * (q ^ 2 * (s.card : ENNReal)) *
        frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K.toConvexSpaceBody := by
    simpa [A, q] using
      one_le_tubeCapacity_mul_frostman hdim htau0 htau1 htheta0 hs W K hWK
  have hCF' :
      frostmanConstIn s (fun i => (W i).toConvexSpaceBody) K.toConvexSpaceBody ≤
        L * q ^ (-eta) := by
    simpa only [L, hinv] using hCF
  simpa [A, L, q] using
    normalizedQ_lower_of_capacity hA0 hAtop hL0 hLtop hq0 hqtop hcap hCF'

end Kakeya.ml1Boot.W47EndpointLowCard

namespace Kakeya.ml1Boot.W48OldFibreProtectedStop

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem frostmanConstIn_freshAncestor_le
    (hdim : Module.finrank Real E = 3)
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} [DecidableEq iota]
    {sU : Finset iota} {Tbase : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet sU Tbase N C) (hsU : sU.Nonempty)
    {sigma j : Nat} (hj : j <= sigma) (hsigma : sigma <= N)
    {source : Finset iota} {W : iota -> ConvexSpaceBody E}
    {q : iota} (hq : q ∈ U.cover.indexSet sigma)
    (hsource : ∀ k ∈ source,
      W k <= (U.cover.tube sigma q).toConvexSpaceBody)
    {A : ENNReal}
    (hold : frostmanConstIn source W
      (U.cover.tube sigma q).toConvexSpaceBody <= A) :
    frostmanConstIn source W
        (U.cover.tube j (U.nodeAncestor sigma j q)).toConvexSpaceBody <=
      (loadToDensity.C 3 : ENNReal) *
        (((Tube.gridScale delta N j / Tube.gridScale delta N sigma : NNReal) :
          ENNReal) ^ (2 : Nat)) * A := by
  let Kold : ConvexSpaceBody E := (U.cover.tube sigma q).toConvexSpaceBody
  let Kfresh : ConvexSpaceBody E :=
    (U.cover.tube j (U.nodeAncestor sigma j q)).toConvexSpaceBody
  let R : ENNReal :=
    (((Tube.gridScale delta N j / Tube.gridScale delta N sigma : NNReal) :
      ENNReal) ^ (2 : Nat))
  have hOldFresh : Kold <= Kfresh :=
    U.tube_le_tube_nodeAncestor hj hsigma hsU hq
  have hOldPos : 0 < volume Kold.carrier :=
    (Tube.volume_pos_and_lt_top
      (Tube.gridScale_pos hdelta0 N sigma)
      (Tube.gridScale_le_one hdelta1 N sigma)
      (U.cover.tube sigma q)).1
  have hOld0 : volume Kold.carrier ≠ 0 := hOldPos.ne'
  have hOldTop : volume Kold.carrier ≠ ⊤ := Kold.isCompact'.measure_ne_top
  have hvolRaw := Tube.volume_le_ratio_mul_volume
    (E := E)
    (Tube.gridScale_le_one hdelta1 N j)
    (Tube.gridScale_pos hdelta0 N sigma)
    (U.cover.tube j (U.nodeAncestor sigma j q))
    (U.cover.tube sigma q)
  have hvol : volume Kfresh.carrier <=
      ((loadToDensity.C 3 : ENNReal) * R) * volume Kold.carrier := by
    simpa only [Kfresh, Kold, R, loadToDensity.C, hdim, Nat.reduceSubDiff] using hvolRaw
  have hvolRatio : volume Kfresh.carrier / volume Kold.carrier <=
      (loadToDensity.C 3 : ENNReal) * R := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hOld0) (Or.inl hOldTop)]
    exact hvol
  have hmono : frostmanConstIn source W Kfresh <=
      volume Kfresh.carrier / volume Kold.carrier * frostmanConstIn source W Kold :=
    frostmanConstIn_ambient_mono hOldFresh hOld0 hsource
  calc
    frostmanConstIn source W Kfresh <=
        volume Kfresh.carrier / volume Kold.carrier * frostmanConstIn source W Kold := hmono
    _ <= ((loadToDensity.C 3 : ENNReal) * R) * A := mul_le_mul' hvolRatio hold
    _ = (loadToDensity.C 3 : ENNReal) * R * A := rfl

end

end Kakeya.ml1Boot.W48OldFibreProtectedStop

namespace Kakeya.ml1Boot.WeakCoarseFibreCore

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

structure WeakCoarseNodeParents {iota : Type*} {delta : NNReal}
    {s' : Finset iota} {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s' T N C) (a b : Nat) (pTheta : iota -> iota) : Prop where
  le_index : a <= b
  le_gridLen : b <= N
  nodes_carry_leaf : ∀ k ∈ U.cover.indexSet b,
    ∃ i ∈ s', U.cover.assign b i = k
  assign_comp : ∀ i ∈ s',
    pTheta (U.cover.assign b i) = U.cover.assign a i
  mapsTo : ∀ k ∈ U.cover.indexSet b, pTheta k ∈ U.cover.indexSet a
  le_parent : ∀ k ∈ U.cover.indexSet b,
    (U.cover.tube b k).toConvexSpaceBody <=
      (U.cover.tube a (pTheta k)).toConvexSpaceBody

/-- A hierarchy-aligned endpoint factor packet.  The regularized active class
is chosen by the multiplicity pigeonhole, while the complete hierarchy fibre
supplies the old/fresh Frostman and normalized-Q certificates.  The second
selector is rerun on the same active class at the protected fresh stop. -/

theorem exists_weakCoarseNodeParents
    {iota : Type*} [DecidableEq iota] {delta : NNReal}
    {s' : Finset iota} {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s' T N C) {a b : Nat}
    (hab : a <= b) (hb : b <= N)
    (hnodes : ∀ k ∈ U.cover.indexSet b,
      ∃ i ∈ s', U.cover.assign b i = k) :
    ∃ pTheta : iota -> iota, WeakCoarseNodeParents U a b pTheta := by
  classical
  obtain ⟨pTheta, hcomp, hmaps, hle⟩ :=
    exists_coarseNodeMap U hab hb (U.cover.indexSet b) hnodes
  exact ⟨pTheta,
    { le_index := hab
      le_gridLen := hb
      nodes_carry_leaf := hnodes
      assign_comp := hcomp
      mapsTo := hmaps
      le_parent := hle }⟩

/-- Canonical ancestor synchronization only needs the assignment identity. -/
theorem nodeAncestor_eq_weakParentMap
    {iota : Type*} [DecidableEq iota] {delta C : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat}
    (U : Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {a b : Nat} {pTheta : iota -> iota}
    (hparents : WeakCoarseNodeParents U a b pTheta)
    {k : iota} (hk : k ∈ U.cover.indexSet b) :
    U.nodeAncestor b a k = pTheta k := by
  obtain ⟨i, hi, hik⟩ := hparents.nodes_carry_leaf k hk
  have hancestor := Kakeya.WangZahl.nodeAncestor_assign_eq U hs
    hparents.le_index hparents.le_gridLen hi
  have hparent := hparents.assign_comp i hi
  rw [hik] at hancestor hparent
  exact hancestor.trans hparent.symm

theorem fibre_eq_tauAncestorClass_of_weakParents
    {iota : Type*} [DecidableEq iota] {delta C : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat}
    (U : Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {a b : Nat} {pTheta : iota -> iota}
    (hparents : WeakCoarseNodeParents U a b pTheta)
    {nodes : Finset iota} (hnodes : nodes ⊆ U.cover.indexSet b) (q : iota) :
    fibre nodes pTheta q =
      Kakeya.WangZahl.tauAncestorClass U b a nodes q := by
  classical
  ext k
  constructor
  · intro hk
    have hk' : k ∈ nodes ∧ pTheta k = q := by simpa [fibre] using hk
    exact (Kakeya.WangZahl.mem_tauAncestorClass U b a nodes q k).mpr
      ⟨hk'.1,
        (nodeAncestor_eq_weakParentMap U hs hparents (hnodes hk'.1)).trans hk'.2⟩
  · intro hk
    have hk' := (Kakeya.WangZahl.mem_tauAncestorClass U b a nodes q k).mp hk
    have hsync := nodeAncestor_eq_weakParentMap U hs hparents (hnodes hk'.1)
    simpa [fibre] using ⟨hk'.1, hsync.symm.trans hk'.2⟩

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem branching_le_mul_card_coarseFibre_weak
    {iota : Type*} [DecidableEq iota] {delta : NNReal}
    {s' : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s' T N C) {pTheta : iota -> iota}
    (hcnp : WeakCoarseNodeParents U a b pTheta)
    {q : iota} (hq : q ∈ U.cover.indexSet a) :
    (U.branchingN a : Real) <=
      (C : Real) ^ 2 * (U.branchingN b : Real) *
        ((fibre (U.cover.indexSet b) pTheta q).card : Real) := by
  classical
  set F : Finset iota := fibre (U.cover.indexSet b) pTheta q
  let cls : iota -> Finset iota := fun k => coverClass s' (U.cover.assign b) k
  have hleN : a <= N := hcnp.le_index.trans hcnp.le_gridLen
  have hsplit : coverClass s' (U.cover.assign a) q = F.biUnion cls := by
    classical
    ext i
    constructor
    · intro h
      have h_mem : i ∈ s' ∧ U.cover.assign a i = q := by
        simpa [coverClass, Finset.mem_filter] using h
      rw [Finset.mem_biUnion]
      refine ⟨U.cover.assign b i, ?_, ?_⟩
      · simpa [F, fibre, Finset.mem_filter] using
          ⟨U.cover.assign_mem b hcnp.le_gridLen i h_mem.1, by
            rw [hcnp.assign_comp i h_mem.1]
            exact h_mem.2⟩
      · simpa [cls, coverClass, Finset.mem_filter] using
          (⟨h_mem.1, rfl⟩ : i ∈ s' ∧ U.cover.assign b i = U.cover.assign b i)
    · intro h
      rw [Finset.mem_biUnion] at h
      rcases h with ⟨k, hk, hik⟩
      have hk_mem : k ∈ U.cover.indexSet b ∧ pTheta k = q := by
        simpa [F, fibre, Finset.mem_filter] using hk
      have hik_mem : i ∈ s' ∧ U.cover.assign b i = k := by
        simpa [cls, coverClass, Finset.mem_filter] using hik
      simpa [coverClass, Finset.mem_filter] using ⟨hik_mem.1, by
        calc
          U.cover.assign a i = pTheta (U.cover.assign b i) :=
            (hcnp.assign_comp i hik_mem.1).symm
          _ = pTheta k := by rw [hik_mem.2]
          _ = q := hk_mem.2⟩
  have hpd : (F : Set iota).PairwiseDisjoint cls := by
    intro k1 hk1 k2 hk2 hne
    change Disjoint (cls k1) (cls k2)
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hm1 : i ∈ s' ∧ U.cover.assign b i = k1 := by
      simpa [cls, coverClass] using hi1
    have hm2 : i ∈ s' ∧ U.cover.assign b i = k2 := by
      simpa [cls, coverClass] using hi2
    exact hne (hm1.2.symm.trans hm2.2)
  have hcard : (coverClass s' (U.cover.assign a) q).card =
      ∑ k ∈ F, (cls k).card := by
    rw [hsplit]
    exact Finset.card_biUnion hpd
  have hsumR : ((coverClass s' (U.cover.assign a) q).card : Real) =
      ∑ k ∈ F, ((cls k).card : Real) := by
    exact_mod_cast hcard
  have hlow : (U.branchingN a : Real) <=
      (C : Real) * ∑ k ∈ F, ((cls k).card : Real) := by
    have h1 : (U.branchingN a : Real) <=
        (C : Real) * ((coverClass s' (U.cover.assign a) q).card : Real) := by
      exact_mod_cast U.le_card_class a hleN q hq
    calc
      (U.branchingN a : Real) <=
          (C : Real) * ((coverClass s' (U.cover.assign a) q).card : Real) := h1
      _ = (C : Real) * (∑ k ∈ F, ((cls k).card : Real)) := by rw [hsumR]
  have hsumle : (∑ k ∈ F, ((cls k).card : Real)) <=
      (F.card : Real) * (C : Real) * (U.branchingN b : Real) := by
    calc
      (∑ k ∈ F, ((cls k).card : Real)) <=
          ∑ k ∈ F, ((C : Real) * (U.branchingN b : Real)) := by
        exact Finset.sum_le_sum (by
          intro k hk
          have hk_index : k ∈ U.cover.indexSet b := (Finset.mem_filter.mp hk).1
          exact_mod_cast U.card_class_le b hcnp.le_gridLen k hk_index)
      _ = (F.card : Real) * (C : Real) * (U.branchingN b : Real) := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
        ring
  calc
    (U.branchingN a : Real) <=
        (C : Real) * ∑ k ∈ F, ((cls k).card : Real) := hlow
    _ <= (C : Real) * ((F.card : Real) * (C : Real) * (U.branchingN b : Real)) := by
      exact mul_le_mul_of_nonneg_left hsumle (by positivity)
    _ = (C : Real) ^ 2 * (U.branchingN b : Real) * (F.card : Real) := by ring

omit [MeasurableSpace E] [BorelSpace E] in
theorem card_nodesIn_le_card_coarseFibre_weak
    {iota : Type*} [DecidableEq iota] {delta : NNReal}
    {s' : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (hC : 1 <= C) (U : Tube.UniformTubeSet s' T N C)
    {pTheta : iota -> iota} (hcnp : WeakCoarseNodeParents U a b pTheta)
    {q : iota} (hq : q ∈ U.cover.indexSet a) :
    fibre (U.cover.indexSet b) pTheta q ⊆
        U.nodesIn b (U.cover.tube a q).toConvexSpaceBody ∧
      ((U.nodesIn b (U.cover.tube a q).toConvexSpaceBody).card : Real) <=
        (C : Real) ^ 5 * ((fibre (U.cover.indexSet b) pTheta q).card : Real) := by
  constructor
  · intro k hk
    rw [fibre] at hk
    have hk_index : k ∈ U.cover.indexSet b := (Finset.mem_filter.mp hk).1
    have hk_parent : pTheta k = q := (Finset.mem_filter.mp hk).2
    rw [Tube.UniformTubeSet.nodesIn, Finset.mem_filter]
    exact ⟨hk_index, by simpa [hk_parent] using hcnp.le_parent k hk_index⟩
  · classical
    let NI : Finset iota := U.nodesIn b (U.cover.tube a q).toConvexSpaceBody
    let F : Finset iota := fibre (U.cover.indexSet b) pTheta q
    let B : Real := (U.branchingN b : Real)
    by_cases hNi : NI.card = 0
    · have h0f : (0 : Real) <= ((fibre (U.cover.indexSet b) pTheta q).card : Real) :=
        Nat.cast_nonneg _
      have h0c : (0 : Real) <= (C : Real) ^ 5 := pow_nonneg (NNReal.coe_nonneg C) 5
      rw [hNi]
      simpa using mul_nonneg h0c h0f
    · have hNe : NI.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hNi)
      rcases hNe with ⟨k0, hk0⟩
      have hk0m : k0 ∈ (U.cover.indexSet b).filter (fun j =>
          (U.cover.tube b j).toConvexSpaceBody <=
            (U.cover.tube a q).toConvexSpaceBody) := by
        simpa [NI, Tube.UniformTubeSet.nodesIn] using hk0
      have hk0index : k0 ∈ U.cover.indexSet b := (Finset.mem_filter.mp hk0m).1
      rcases hcnp.nodes_carry_leaf k0 hk0index with ⟨i, hi, hassign⟩
      let cls_k : Finset iota := coverClass s' (U.cover.assign b) k0
      have hi_c : i ∈ cls_k := by simpa [cls_k, coverClass, hassign] using hi
      have hcls_pos : 0 < cls_k.card := Finset.card_pos.mpr ⟨i, hi_c⟩
      have hOne : (1 : Real) <= (C : Real) * B := by
        have hge : (1 : NNReal) <= (cls_k.card : NNReal) := by
          exact_mod_cast (Nat.succ_le_of_lt hcls_pos)
        have hle : (cls_k.card : NNReal) <= C * U.branchingN b :=
          U.card_class_le b hcnp.le_gridLen k0 hk0index
        exact_mod_cast (le_trans hge hle)
      have hCpos : 0 < (C : Real) :=
        lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (by exact_mod_cast hC)
      have hBpos : 0 < B := by
        have hcm : 0 < (C : Real) * B := lt_of_lt_of_le (by norm_num) hOne
        exact pos_of_mul_pos_right hcm (le_of_lt hCpos)
      have h1 : B * (NI.card : Real) <=
          (C : Real) ^ 3 * (U.branchingN a : Real) := by
        simpa [B, NI] using
          branching_mul_card_nodesIn_le U hcnp.le_index hcnp.le_gridLen q
      have h2 : (U.branchingN a : Real) <=
          (C : Real) ^ 2 * B * (F.card : Real) := by
        simpa [B, F] using branching_le_mul_card_coarseFibre_weak U hcnp hq
      have h2' : (C : Real) ^ 3 * (U.branchingN a : Real) <=
          (C : Real) ^ 5 * B * (F.card : Real) := by
        calc
          (C : Real) ^ 3 * (U.branchingN a : Real) <=
              (C : Real) ^ 3 * ((C : Real) ^ 2 * B * (F.card : Real)) := by
            exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (le_of_lt hCpos) 3)
          _ = (C : Real) ^ 5 * B * (F.card : Real) := by ring
      have hchain : B * (NI.card : Real) <=
          (C : Real) ^ 5 * B * (F.card : Real) := le_trans h1 h2'
      have hbm : B * (NI.card : Real) <=
          B * ((C : Real) ^ 5 * (F.card : Real)) := by
        simpa [mul_comm, mul_assoc, mul_left_comm] using hchain
      exact le_of_mul_le_mul_left hbm hBpos

theorem frostmanConstIn_coarseFibre_le_weak
    {iota : Type*} [DecidableEq iota] {delta : NNReal}
    {s' : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (hC : 1 <= C) (U : Tube.UniformTubeSet s' T N C)
    {pTheta : iota -> iota} (hcnp : WeakCoarseNodeParents U a b pTheta)
    {q : iota} (hq : q ∈ U.cover.indexSet a)
    (hne : (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody).Nonempty) :
    frostmanConstIn (fibre (U.cover.indexSet b) pTheta q)
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      (C : ENNReal) ^ 5 *
        frostmanConstIn (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody)
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody := by
  classical
  set sBase : Finset iota := U.nodesIn b (U.cover.tube a q).toConvexSpaceBody
  set sFibre : Finset iota := fibre (U.cover.indexSet b) pTheta q
  set Wb : iota -> ConvexSpaceBody E := fun k => (U.cover.tube b k).toConvexSpaceBody
  set Ka : ConvexSpaceBody E := (U.cover.tube a q).toConvexSpaceBody
  set kappa : ENNReal := ((C : ENNReal) ^ 5)⁻¹
  let volume0 : ENNReal := volume (U.cover.tube b hne.choose).carrier
  have hC5_ne0 : (C : ENNReal) ^ 5 ≠ 0 := by
    have hC0 : (C : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hC))
    exact pow_ne_zero 5 hC0
  have hC5_ne_top : (C : ENNReal) ^ 5 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hkappa_ne : kappa ≠ 0 := by
    dsimp [kappa]
    exact ENNReal.inv_ne_zero.mpr hC5_ne_top
  have hcount : sFibre ⊆ sBase ∧
      (sBase.card : Real) <= (C : Real) ^ 5 * (sFibre.card : Real) := by
    simpa [sBase, sFibre] using card_nodesIn_le_card_coarseFibre_weak hC U hcnp hq
  have hvol : ∀ i ∈ sBase, volume (Wb i).carrier = volume0 := by
    intro i hi
    simpa [Wb, volume0, sBase] using
      Tube.volume_carrier_eq_volume_carrier (U.cover.tube b i)
        (U.cover.tube b hne.choose)
  have hWK : ∀ i ∈ sBase, Wb i <= Ka := by
    intro i hi
    have hmem : i ∈ U.cover.indexSet b ∧
        (U.cover.tube b i).toConvexSpaceBody <= Ka := by
      simpa [sBase, Tube.UniformTubeSet.nodesIn] using hi
    simpa [Wb] using hmem.2
  have hcard_nn : (sBase.card : NNReal) <=
      (C : NNReal) ^ 5 * (sFibre.card : NNReal) := by exact_mod_cast hcount.2
  have hcard_enn : (sBase.card : ENNReal) <=
      (C : ENNReal) ^ 5 * (sFibre.card : ENNReal) := ENNReal.coe_le_coe.mpr hcard_nn
  have hcard : kappa * (sBase.card : ENNReal) <= (sFibre.card : ENNReal) := by
    calc
      kappa * (sBase.card : ENNReal) <=
          kappa * ((C : ENNReal) ^ 5 * (sFibre.card : ENNReal)) :=
        mul_le_mul_right hcard_enn kappa
      _ = (sFibre.card : ENNReal) := by
        dsimp [kappa]
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC5_ne0 hC5_ne_top, one_mul]
  have hsub : frostmanConstIn sFibre Wb Ka <=
      kappa⁻¹ * frostmanConstIn sBase Wb Ka := by
    exact frostmanConstIn_subfamily_le hne hvol hWK hcount.1 hkappa_ne hcard
  calc
    frostmanConstIn sFibre Wb Ka <= kappa⁻¹ * frostmanConstIn sBase Wb Ka := hsub
    _ = (C : ENNReal) ^ 5 * frostmanConstIn sBase Wb Ka := by simp [kappa]

theorem caseTwoRawMidFibre_weak
    (p : Params) {epsPrime : Real} (hepsPrime : 0 < epsPrime)
    {C : NNReal} (hC : 1 <= C) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {iota : Type u} [DecidableEq iota] {s' : Finset iota}
        {T : iota -> Tube delta E} {N : Nat}
        (a b m : Nat) (U : Tube.UniformTubeSet s' T N C)
        (pTheta : iota -> iota),
        WeakCoarseNodeParents U a b pTheta ->
        (∀ q ∈ U.cover.indexSet a,
          frostmanConstIn (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody)
              (fun k => (U.cover.tube b k).toConvexSpaceBody)
              (U.cover.tube a q).toConvexSpaceBody <=
            (delta : ENNReal) ^ (-epsPrime) *
              ((Tube.gridScale delta N a / Tube.gridScale delta N b : NNReal) : ENNReal) ^
                p.η m) ->
        ∀ q ∈ U.cover.indexSet a,
          (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody).Nonempty ->
          frostmanConstIn (fibre (U.cover.indexSet b) pTheta q)
              (fun k => (U.cover.tube b k).toConvexSpaceBody)
              (U.cover.tube a q).toConvexSpaceBody <=
            (delta : ENNReal) ^ (-2 * epsPrime) *
              ((Tube.gridScale delta N a / Tube.gridScale delta N b : NNReal) : ENNReal) ^
                p.η m := by
  have hCabs : ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      (C : ENNReal) ^ (5 : Nat) <= (delta : ENNReal) ^ (-epsPrime) := by
    have hCposR : (0 : Real) < (C : Real) ^ (5 : Nat) := by positivity
    filter_upwards [nnreal_eventually_of_real_eventually
        (Kakeya.absorb_const_le_rpow_neg hCposR hepsPrime), self_mem_nhdsWithin]
      with delta hcst hdelta0
    have hdeltaR : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta0
    rw [ennreal_coe_nnreal_rpow hdeltaR (-epsPrime)]
    calc
      (C : ENNReal) ^ (5 : Nat) = ENNReal.ofReal ((C : Real) ^ (5 : Nat)) := by
        rw [← ENNReal.ofReal_coe_nnreal (p := C), ENNReal.ofReal_pow]
        positivity
      _ <= ENNReal.ofReal ((delta : Real) ^ (-epsPrime)) := ENNReal.ofReal_le_ofReal hcst
  filter_upwards [hCabs, self_mem_nhdsWithin] with delta hCabsDelta hdelta0
  intro iota _ s' T N a b m U pTheta hcnp hraw q hq hne
  have hdeltaNe : ((delta : NNReal) : ENNReal) ≠ 0 :=
    ne_of_gt (ENNReal.coe_pos.mpr hdelta0)
  set ratio : ENNReal :=
    ((Tube.gridScale delta N a / Tube.gridScale delta N b : NNReal) : ENNReal) ^ p.η m
  have hfib := frostmanConstIn_coarseFibre_le_weak hC U hcnp hq hne
  have hmid : frostmanConstIn (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody)
      (fun k => (U.cover.tube b k).toConvexSpaceBody)
      (U.cover.tube a q).toConvexSpaceBody <=
      (delta : ENNReal) ^ (-epsPrime) * ratio := hraw q hq
  have hcoef : (C : ENNReal) ^ (5 : Nat) * (delta : ENNReal) ^ (-epsPrime) <=
      (delta : ENNReal) ^ (-epsPrime) * (delta : ENNReal) ^ (-epsPrime) :=
    mul_le_mul_of_nonneg_right hCabsDelta (by positivity)
  calc
    frostmanConstIn (fibre (U.cover.indexSet b) pTheta q)
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      (C : ENNReal) ^ 5 *
        frostmanConstIn (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody)
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody := hfib
    _ <= (C : ENNReal) ^ 5 * ((delta : ENNReal) ^ (-epsPrime) * ratio) := by gcongr
    _ = ((C : ENNReal) ^ 5 * (delta : ENNReal) ^ (-epsPrime)) * ratio := by ac_rfl
    _ <= ((delta : ENNReal) ^ (-epsPrime) *
        (delta : ENNReal) ^ (-epsPrime)) * ratio := by gcongr
    _ = (delta : ENNReal) ^ (-2 * epsPrime) * ratio := by
      have hpow : (delta : ENNReal) ^ (-epsPrime) *
          (delta : ENNReal) ^ (-epsPrime) =
          (delta : ENNReal) ^ (-2 * epsPrime) := by
        rw [← ENNReal.rpow_add (-epsPrime) (-epsPrime) hdeltaNe ENNReal.coe_ne_top]
        congr 1
        ring
      rw [hpow]

/-- Complete old source at a caller-selected active parent.  This is the
alignment interface needed by the endpoint hierarchy factor: the active
regularized class remains available for the multiplicity bridge, while all
Frostman and Q estimates are proved on its containing complete hierarchy fibre. -/
theorem eventually_exists_completeOldFibreFreshCore_at_active_weak_w48
    (hdim : Module.finrank Real E = 3)
    {p : Params} {epsPrime : Real} (hepsPrime : 0 < epsPrime)
    (Cds : NNReal) (hCds : 1 <= Cds) (Kds cds : Nat) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {iota : Type u} [DecidableEq iota] {s' : Finset iota}
        (T : iota -> ShadedTube delta E)
        (U : Tube.UniformTubeSet s' (fun i => (T i).toTube)
          (Tube.ssfGridLen delta) Cds)
        (a b m : Nat) (pTheta : iota -> iota),
        StickyKakeya.IsFrostmanDividingBlock U Cds Kds cds p.η p.ε a b m p.N ->
        WeakCoarseNodeParents U a b pTheta ->
        s'.Nonempty ->
        ∀ {mid : Finset iota}, mid ⊆ U.cover.indexSet b ->
        ∀ {q : iota}, q ∈ Kakeya.WangZahl.activeRhoParents U b a mid ->
        ∃ j parent,
          let active := Kakeya.WangZahl.tauAncestorClass U b a mid q
          let source := fibre (U.cover.indexSet b) pTheta q
          let Araw : ENNReal :=
            (delta : ENNReal) ^ (-2 * epsPrime) *
              ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
                Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ENNReal) ^ p.η m
          let q0 : ENNReal :=
            (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
                (delta : ENNReal) ^ (-2 * epsPrime))⁻¹ *
              ((Tube.gridScale delta (Tube.ssfGridLen delta) b /
                Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) : ENNReal) ^ p.η m
          active.Nonempty ∧ active ⊆ source ∧
          source.Nonempty ∧ source ⊆ U.cover.indexSet b ∧
          source = Kakeya.WangZahl.tauAncestorClass U b a
            (U.cover.indexSet b) q ∧
          j <= a ∧ parent = U.nodeAncestor a j q ∧
          Kakeya.WangZahl.tauAncestorClass U b j source parent = source ∧
          Kakeya.WangZahl.hierarchyGlobalCrossing U b source q0.toNNReal j ∧
          frostmanConstIn source
              (fun k => (U.cover.tube b k).toConvexSpaceBody)
              (U.cover.tube a q).toConvexSpaceBody <= Araw ∧
          frostmanConstIn source
              (fun k => (U.cover.tube b k).toConvexSpaceBody)
              (U.cover.tube j parent).toConvexSpaceBody <=
            (loadToDensity.C 3 : ENNReal) *
              (((Tube.gridScale delta (Tube.ssfGridLen delta) j /
                Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) : ENNReal) ^
                  (2 : Nat)) * Araw ∧
          q0 <=
            ((((Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) j) ^ 2 *
                (Kakeya.WangZahl.tauAncestorClass U b j source parent).card : NNReal) :
                  ENNReal)) ∧
          (j = 0 ∨
            ((((Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) j) ^ 2 *
                (Kakeya.WangZahl.tauAncestorClass U b j source parent).card : NNReal) :
                  ENNReal)) <
              q0 *
                (((Tube.gridScale delta (Tube.ssfGridLen delta) (j - 1) /
                  Tube.gridScale delta (Tube.ssfGridLen delta) j) ^ 2 : NNReal) :
                    ENNReal)) := by
  classical
  filter_upwards [
      Kakeya.ml1Boot.W51RawMiddleBlock.caseTwoRawMid_of_block_upstream_w51
        (E := E) hepsPrime Cds Kds cds,
      caseTwoRawMidFibre_weak (E := E) p hepsPrime hCds,
      self_mem_nhdsWithin, eventually_le_one_nhdsGT]
    with delta hraw hrawFibre hdelta0 hdelta1
  intro iota _ s' T U a b m pTheta hblock hparents hs' mid hmidNodes q hq
  have hqA : q ∈ U.cover.indexSet a :=
    Kakeya.WangZahl.activeRhoParents_subset_indexSet U hs'
      (hparents.le_index.trans hparents.le_gridLen) hparents.le_gridLen hmidNodes hq
  let active := Kakeya.WangZahl.tauAncestorClass U b a mid q
  let source := fibre (U.cover.indexSet b) pTheta q
  let Araw : ENNReal :=
    (delta : ENNReal) ^ (-2 * epsPrime) *
      ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
        Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ENNReal) ^ p.η m
  let q0 : ENNReal :=
    (((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-2 * epsPrime))⁻¹ *
      ((Tube.gridScale delta (Tube.ssfGridLen delta) b /
        Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) : ENNReal) ^ p.η m
  have hactiveNe : active.Nonempty := by
    exact Kakeya.WangZahl.tauAncestorClass_nonempty U b a mid hq
  have hactiveEq : active = fibre mid pTheta q := by
    symm
    simpa only [active] using
      fibre_eq_tauAncestorClass_of_weakParents U hs' hparents hmidNodes q
  have hsourceNe : source.Nonempty := by
    exact hactiveNe.mono (fun k hk => by
      rw [hactiveEq] at hk
      exact Finset.mem_filter.mpr
        ⟨hmidNodes (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩)
  have hactiveSource : active ⊆ source := by
    intro k hk
    rw [hactiveEq] at hk
    exact Finset.mem_filter.mpr
      ⟨hmidNodes (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  have hsourceNodes : source ⊆ U.cover.indexSet b := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hsourceOld : source = Kakeya.WangZahl.tauAncestorClass U b a
      (U.cover.indexSet b) q := by
    simpa only [source] using
      fibre_eq_tauAncestorClass_of_weakParents U hs' hparents (by rfl) q
  have hrawNodes : ∀ q' ∈ U.cover.indexSet a,
      frostmanConstIn (U.nodesIn b (U.cover.tube a q').toConvexSpaceBody)
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q').toConvexSpaceBody <=
        (delta : ENNReal) ^ (-epsPrime) *
          ((Tube.gridScale delta (Tube.ssfGridLen delta) a /
            Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : ENNReal) ^ p.η m := by
    intro q' hq'
    rw [← familyIn_indexSet_eq_nodesIn U b (U.cover.tube a q').toConvexSpaceBody]
    exact hraw T U a b m hblock q' hq'
  have hnodesIn : (U.nodesIn b (U.cover.tube a q).toConvexSpaceBody).Nonempty :=
    hsourceNe.mono (card_nodesIn_le_card_coarseFibre_weak hCds U hparents hqA).1
  have hsourceFrost : frostmanConstIn source
      (fun k => (U.cover.tube b k).toConvexSpaceBody)
      (U.cover.tube a q).toConvexSpaceBody <= Araw := by
    simpa only [source, Araw] using
      hrawFibre a b m U pTheta hparents hrawNodes q hqA hnodesIn
  have htau0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    Tube.gridScale_pos hdelta0 _ _
  have htau1 : Tube.gridScale delta (Tube.ssfGridLen delta) b <= 1 :=
    Tube.gridScale_le_one hdelta1 _ _
  have htheta0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) a :=
    Tube.gridScale_pos hdelta0 _ _
  have hcontain : ∀ k ∈ source,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a q).toConvexSpaceBody := by
    intro k hk
    obtain ⟨hkb, hkq⟩ := Finset.mem_filter.mp hk
    have hle := hparents.le_parent k hkb
    rwa [hkq] at hle
  have hQold : q0 <=
      (((Tube.gridScale delta (Tube.ssfGridLen delta) b /
        Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) : ENNReal) ^ 2 *
          (source.card : ENNReal)) := by
    simpa only [q0] using
      W47EndpointLowCard.completeFibre_normalizedQ_lower_of_frostman
        hdim hdelta0 htau0 htau1 htheta0 hsourceNe
          (U.cover.tube b) (U.cover.tube a q) hcontain hsourceFrost
  have hgeomPos : 0 < Tube.volume_le.C 3 / Tube.le_volume.c 3 :=
    div_pos (Tube.volume_le.C_pos 3) (Tube.le_volume.c_pos 3)
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hq0Top : q0 ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · rw [ENNReal.inv_ne_top]
      exact mul_ne_zero (ENNReal.coe_ne_zero.mpr hgeomPos.ne')
        (by simp [ENNReal.rpow_eq_zero_iff, hdeltaE0])
    · exact ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.coe_ne_zero.mpr
          (div_pos (Tube.gridScale_pos hdelta0 _ b)
            (Tube.gridScale_pos hdelta0 _ a)).ne') ENNReal.coe_ne_top
  obtain ⟨j, parent, hj, hcross, hparent, hcore, hQlow, hQupper⟩ :=
    Kakeya.ml1Boot.W48ReverseQBand.exists_firstProtectedCrossing_with_exact_QBand_or_top
      U hdelta0 hs' hparents.le_index hparents.le_gridLen (by rfl)
        hsourceNe hsourceOld hq0Top hQold
  have hfresh := W48OldFibreProtectedStop.frostmanConstIn_freshAncestor_le
    hdim hdelta0 hdelta1 U hs' hj
      (hparents.le_index.trans hparents.le_gridLen)
      (W := fun k => (U.cover.tube b k).toConvexSpaceBody) hqA
      hcontain hsourceFrost
  refine ⟨j, parent, ?_⟩
  dsimp only
  exact ⟨hactiveNe, hactiveSource, hsourceNe, hsourceNodes, hsourceOld,
    hj, hparent, hcore, hcross, hsourceFrost,
    by simpa only [hparent] using hfresh, hQlow, hQupper⟩

end

end Kakeya.ml1Boot.WeakCoarseFibreCore

namespace Kakeya.ml1Boot.W48SelectedFreshStopProducer

noncomputable section
set_option maxHeartbeats 8000000

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem zeroExtended_input_fullness_lower_of_ballMassRetention
    {iota : Type u} {rho : NNReal} (hrho0 : 0 < rho) (hrho1 : rho <= 1)
    [DecidableEq iota] {core u : Finset iota} (hcore : core.Nonempty) (hu : u ⊆ core)
    {Tbase : iota -> Tube rho E} {Z : iota -> ShadedTube rho E} {v : E} {D : ENNReal}
    (hTbase : ∀ k ∈ core, Tbase k = (Z k).toTube)
    (hmass : (∑ k ∈ core, volume (Z k).shade) <=
      D * ∑ k ∈ u, volume ((Z k).translate v).shade) :
    (ShadedBody.fullness core (fun k => (Z k).toShadedBody) : ENNReal) <=
      D * (ShadedBody.fullness core
        (fun k => (zeroExtend u (fun j => (Tbase j).translate v)
          (fun j => (Z j).translate v) k).toShadedBody) : ENNReal) := by
  classical
  obtain ⟨k0, hk0⟩ := hcore
  have hcoreNe : core.Nonempty := ⟨k0, hk0⟩
  let vol0 : ENNReal := volume (Z k0).carrier
  have hvol0 : 0 < vol0 := by
    exact (tube_volume_pos_ne_top (E := E) hrho0 (Z k0).toTube).1
  have hvol0top : vol0 ≠ ⊤ := by
    exact (tube_volume_pos_ne_top (E := E) hrho0 (Z k0).toTube).2
  have hcoreCard0 : (core.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hcoreNe).ne'
  have hden0 : (core.card : ENNReal) * vol0 ≠ 0 :=
    mul_ne_zero hcoreCard0 hvol0.ne'
  have hdenTop : (core.card : ENNReal) * vol0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvol0top
  have hsumCore : ∑ k ∈ core, volume (Z k).carrier =
      (core.card : ENNReal) * vol0 := by
    simpa [vol0] using Tube.sum_volume_carrier_eq_card_mul
      (fun k => (Z k).toTube) (Z k0).toTube core
  have hnumZero :
      ∑ k ∈ core,
          volume (zeroExtend u (fun j => (Tbase j).translate v)
            (fun j => (Z j).translate v) k).shade =
        ∑ k ∈ u, volume ((Z k).translate v).shade := by
    exact sum_volume_shade_zeroExtend_of_subset hu _ _
  have hdenZero :
      ∑ k ∈ core,
          volume (zeroExtend u (fun j => (Tbase j).translate v)
            (fun j => (Z j).translate v) k).carrier =
        (core.card : ENNReal) * vol0 := by
    calc
      ∑ k ∈ core,
          volume (zeroExtend u (fun j => (Tbase j).translate v)
            (fun j => (Z j).translate v) k).carrier =
          ∑ k ∈ core, volume ((Tbase k).translate v).carrier := by
            apply Finset.sum_congr rfl
            intro k hk
            exact volume_carrier_zeroExtend _ _ _ k
      _ = (core.card : ENNReal) * volume ((Tbase k0).translate v).carrier := by
        exact Tube.sum_volume_carrier_eq_card_mul
          (fun k => (Tbase k).translate v) ((Tbase k0).translate v) core
      _ = (core.card : ENNReal) * vol0 := by
        rw [hTbase k0 hk0]
        simp [vol0, Kakeya.volume_translate]
  rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  change ((∑ k ∈ core, volume (Z k).shade) /
      (∑ k ∈ core, volume (Z k).carrier)) <=
    D * ((∑ k ∈ core,
      volume (zeroExtend u (fun j => (Tbase j).translate v)
        (fun j => (Z j).translate v) k).shade) /
      (∑ k ∈ core,
        volume (zeroExtend u (fun j => (Tbase j).translate v)
          (fun j => (Z j).translate v) k).carrier))
  rw [hsumCore, hnumZero, hdenZero]
  rw [ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdenTop)]
  calc
    (∑ k ∈ core, volume (Z k).shade) <=
        D * ∑ k ∈ u, volume ((Z k).translate v).shade := hmass
    _ = (D * ((∑ k ∈ u, volume ((Z k).translate v).shade) /
          ((core.card : ENNReal) * vol0))) *
        ((core.card : ENNReal) * vol0) := by
      rw [mul_assoc, ENNReal.div_mul_cancel hden0 hdenTop]

/-- BallPort's retained shade mass directly funds the fullness field of the actual
second selected family on the whole zero-extended core. -/
theorem secondSelected_lam_lower_of_ballMassRetention
    {iota : Type u} {kappa : Type w} [DecidableEq iota] [DecidableEq kappa]
    {tau rho : NNReal} (htau0 : 0 < tau) (htau1 : tau <= 1)
    {core u : Finset iota} (hcore : core.Nonempty) (hu : u ⊆ core)
    {Tbase : iota -> Tube tau E} {Z : iota -> ShadedTube tau E} {v : E}
    (hTbase : ∀ k ∈ core, Tbase k = (Z k).toTube)
    {D c2 L2 : ENNReal}
    (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hmass : (∑ k ∈ core, volume (Z k).shade) <=
      D * ∑ k ∈ u, volume ((Z k).translate v).shade)
    {tAmb tAct : Finset kappa} {Vrho : kappa -> Tube rho E}
    {pMap : iota -> kappa} {act' : Finset iota}
    {Z' : iota -> ShadedTube tau E} {Zrho : kappa -> ShadedTube rho E}
    {k0 : kappa} {lamP lamM : NNReal}
    (h2 : IsOneScaleSelected c2 L2 core u
      (zeroExtend u (fun k => (Tbase k).translate v) (fun k => (Z k).translate v))
      tAmb Vrho pMap act' Z' tAct Zrho k0 lamP lamM) :
    c2 * (D⁻¹ *
      (ShadedBody.fullness core (fun k => (Z k).toShadedBody) : ENNReal)) <=
      (lamM : ENNReal) := by
  have hret := zeroExtended_input_fullness_lower_of_ballMassRetention
    (E := E) htau0 htau1 hcore hu hTbase hmass
  have hscaled : D⁻¹ *
      (ShadedBody.fullness core (fun k => (Z k).toShadedBody) : ENNReal) <=
      (ShadedBody.fullness core
        (fun k => (zeroExtend u (fun j => (Tbase j).translate v)
          (fun j => (Z j).translate v) k).toShadedBody) : ENNReal) := by
    calc
      D⁻¹ * (ShadedBody.fullness core
          (fun k => (Z k).toShadedBody) : ENNReal) <=
          D⁻¹ * (D * (ShadedBody.fullness core
            (fun k => (zeroExtend u (fun j => (Tbase j).translate v)
              (fun j => (Z j).translate v) k).toShadedBody) : ENNReal)) := by
            gcongr
      _ = (ShadedBody.fullness core
          (fun k => (zeroExtend u (fun j => (Tbase j).translate v)
            (fun j => (Z j).translate v) k).toShadedBody) : ENNReal) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]
  calc
    c2 * (D⁻¹ *
        (ShadedBody.fullness core (fun k => (Z k).toShadedBody) : ENNReal)) <=
      c2 * (ShadedBody.fullness core
        (fun k => (zeroExtend u (fun j => (Tbase j).translate v)
          (fun j => (Z j).translate v) k).toShadedBody) : ENNReal) := by gcongr
    _ <= (lamM : ENNReal) := h2.sel_fullness_lb

end

end Kakeya.ml1Boot.W48SelectedFreshStopProducer


namespace Kakeya.ml1Boot.W58QuotientAwareQV5

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

structure WeakCoarseNodeParentsV5W58
    {iota : Type u} {delta : NNReal}
    {sPrime : Finset iota} {T : iota -> Tube delta E}
    {N : Nat} {Cd : NNReal}
    (U : Tube.UniformTubeSet sPrime T N Cd)
    (a b : Nat) (pTheta : iota -> iota) : Prop where
  le_index : a <= b
  le_gridLen : b <= N
  nodes_carry_leaf : forall k, k ∈ U.cover.indexSet b ->
    exists i, i ∈ sPrime /\ U.cover.assign b i = k
  assign_comp : forall i, i ∈ sPrime ->
    pTheta (U.cover.assign b i) = U.cover.assign a i
  mapsTo : forall k, k ∈ U.cover.indexSet b ->
    pTheta k ∈ U.cover.indexSet a
  le_parent : forall k, k ∈ U.cover.indexSet b ->
    (U.cover.tube b k).toConvexSpaceBody <=
      (U.cover.tube a (pTheta k)).toConvexSpaceBody

def normalizedQV5W58 {iota : Type u}
    (q : NNReal) (source : Finset iota) : ENNReal :=
  (q : ENNReal) ^ (2 : Nat) * (source.card : ENNReal)

def activeClassV5W58
    {delta Cd : NNReal} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N : Nat}
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (b a : Nat) (mid : Finset iota) (q : iota) : Finset iota :=
  Kakeya.WangZahl.tauAncestorClass U b a mid q

def completeClassV5W58
    {delta Cd : NNReal} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N : Nat}
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (b a : Nat) (q : iota) : Finset iota :=
  Kakeya.WangZahl.tauAncestorClass U b a (U.cover.indexSet b) q

def retainedShareV5W58 {iota : Type u}
    (active complete : Finset iota) : ENNReal :=
  (active.card : ENNReal) / (complete.card : ENNReal)

def SymmetricCompleteQBandV5W58 {iota : Type u}
    (delta q : NNReal) (complete : Finset iota)
    (CQ : NNReal) (zQ : Real) : Prop :=
  (CQ : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ zQ <=
      normalizedQV5W58 q complete /\
    normalizedQV5W58 q complete <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)

def QuotientScaledActiveQBandV5W58 {iota : Type u}
    (delta q : NNReal) (active : Finset iota)
    (kappa : ENNReal) (CQ : NNReal) (zQ : Real) : Prop :=
  kappa * ((CQ : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ zQ) <=
      normalizedQV5W58 q active /\
    normalizedQV5W58 q active <=
      kappa * ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))

def completeLevelAFrostmanBudgetV5W58
    (delta : NNReal) (N a b m : Nat) (p : Params) : ENNReal :=
  (delta : ENNReal) ^ (-p.ε) *
    ((Tube.gridScale delta N a / Tube.gridScale delta N b : NNReal) : ENNReal) ^ p.η m

structure PreSecondFactorLevelBPacketV5W58
    {delta Cd : NNReal} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N b : Nat}
    (p : Params)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd) where
  tTau : Finset iota
  pTau : iota -> iota
  repTau : iota -> iota
  fineActive : Finset iota
  Zf : iota -> ShadedTube delta E
  tAct : Finset iota
  ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E
  kF : iota
  lamP : NNReal
  lamF : NNReal
  regularizationExponent : Real
  mid : Finset iota
  mu0 : NNReal
  tau_subset : tTau ⊆ U.cover.indexSet b
  tau_map_mem : forall i, pTau i ∈ tTau
  tau_map_is_representative : forall i, i ∈ sPrime ->
    pTau i = repTau (U.cover.assign b i)
  tau_represents_every_body : forall k, k ∈ U.cover.indexSet b ->
    repTau k ∈ tTau /\
      (U.cover.tube b (repTau k)).toConvexSpaceBody =
        (U.cover.tube b k).toConvexSpaceBody
  tau_representative_onto : forall k, k ∈ tTau ->
    exists k0, k0 ∈ U.cover.indexSet b /\ repTau k0 = k
  tau_selected_body : forall i, i ∈ sPrime ->
    (U.cover.tube b (pTau i)).toConvexSpaceBody =
      (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody
  fine_parent : IsParentFamily sPrime (fun i => (V i).toTube)
    tTau (U.cover.tube b) pTau
  lamP_exact : lamP =
    ((1 * factorOneScale.C sPrime.card delta)⁻¹ * delta ^ p.η 0)
  first_factor : IsOneScaleSelected
    ((((factorOneScale.C sPrime.card delta)⁻¹ : NNReal) : ENNReal))
    ((factorOneScale.C sPrime.card delta : NNReal) : ENNReal)
    sPrime sPrime V tTau (U.cover.tube b) pTau
    fineActive Zf tAct ZTau kF lamP lamF
  lamP_funded :
    (delta : ENNReal) ^ regularizationExponent <= (lamP : ENNReal)
  mid_subset : mid ⊆ tAct
  mid_nonempty : mid.Nonempty
  mu0_pos : 0 < mu0
  middle_tube : forall k, k ∈ mid ->
    (ZTau k).toTube = U.cover.tube b k
  density_band : forall k, k ∈ mid ->
    ((2 : NNReal) : ENNReal)⁻¹ * (mu0 : ENNReal) * volume (ZTau k).carrier <=
        volume (ZTau k).shade /\
      volume (ZTau k).shade <=
        ((2 : NNReal) : ENNReal) * (mu0 : ENNReal) * volume (ZTau k).carrier
  regularization_multiplicity :
    ShadedBody.multiplicity tAct (fun k => (ZTau k).toShadedBody) <=
      16 * (delta : ENNReal) ^ (-regularizationExponent) *
        ShadedBody.multiplicity mid (fun k => (ZTau k).toShadedBody)
  regularization_fullness :
    (delta : ENNReal) ^ (2 * regularizationExponent) / 16 <=
      (ShadedBody.fullness mid (fun k => (ZTau k).toShadedBody) : ENNReal)
  regularization_card :
    ((delta : ENNReal) ^ (2 * regularizationExponent) / 16) *
        (tAct.card : ENNReal) <= (mid.card : ENNReal)

structure StoppedTwoSourceV5W58
    {delta Cd : NNReal} {iota : Type u} [DecidableEq iota]
    {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
    {N a b : Nat}
    (p : Params) (m : Nat)
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U) where
  pTheta : iota -> iota
  parents : WeakCoarseNodeParentsV5W58 U a b pTheta
  q : iota
  active : Finset iota
  complete : Finset iota
  j : Nat
  pJ : iota
  q_active : q ∈ Kakeya.WangZahl.activeRhoParents U b a pre.mid
  active_eq : active = activeClassV5W58 U b a pre.mid q
  complete_eq : complete = completeClassV5W58 U b a q
  complete_fibre_eq : complete = fibre (U.cover.indexSet b) pTheta q
  active_nonempty : active.Nonempty
  complete_nonempty : complete.Nonempty
  active_subset_complete : active ⊆ complete
  active_subset_mid : active ⊆ pre.mid
  complete_subset_levelB : complete ⊆ U.cover.indexSet b
  active_mass_pos : 0 < ∑ k ∈ active, volume (pre.ZTau k).shade
  max_multiplicity_paid :
    ShadedBody.multiplicity pre.mid (fun k => (pre.ZTau k).toShadedBody) <=
      ((Kakeya.WangZahl.activeRhoParents U b a pre.mid).card : ENNReal) *
        ShadedBody.multiplicity active (fun k => (pre.ZTau k).toShadedBody)
  kappa : ENNReal
  kappa_eq : kappa = retainedShareV5W58 active complete
  kappa_ne_zero : kappa ≠ 0
  kappa_ne_top : kappa ≠ ⊤
  kappa_le_one : kappa <= 1
  card_share_exact :
    kappa * (complete.card : ENNReal) = (active.card : ENNReal)
  level_le : j <= a
  stopped_parent_eq : pJ = U.nodeAncestor a j q
  stopped_parent_mem : pJ ∈ U.cover.indexSet j
  complete_constant_at_stop : forall k, k ∈ complete ->
    U.nodeAncestor b j k = pJ
  active_constant_at_stop : forall k, k ∈ active ->
    U.nodeAncestor b j k = pJ
  complete_eq_stopped_class :
    Kakeya.WangZahl.tauAncestorClass U b j complete pJ = complete
  active_eq_stopped_class :
    Kakeya.WangZahl.tauAncestorClass U b j active pJ = active
  first_crossing_complete :
    Kakeya.WangZahl.hierarchyGlobalCrossing U b complete
      ((delta : ENNReal) ^ (3 * p.η m)).toNNReal j
  frostman_complete_levelA :
    frostmanConstIn complete
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      completeLevelAFrostmanBudgetV5W58 delta N a b m p
  frostman_active_levelA :
    frostmanConstIn active
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a q).toConvexSpaceBody <=
      kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta N a b m p
  complete_Q_lower_at_a :
    (delta : ENNReal) ^ (3 * p.η m) <=
      normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) complete
  active_Q_lower_at_a_scaled :
    kappa * (delta : ENNReal) ^ (3 * p.η m) <=
      normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) active
  Q_identity_at_a :
    normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) active =
      kappa * normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N a) complete
  Q_identity_at_stop :
    normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N j) active =
      kappa * normalizedQV5W58
        (Tube.gridScale delta N b / Tube.gridScale delta N j) complete
  endpoint_or_nonTop_complete :
    (j = 0 /\ Tube.gridScale delta N j = 1 /\
      (delta : ENNReal) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N j) complete) \/
    (0 < j /\ SymmetricCompleteQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N j)
      complete 1 (3 * p.η m))
  endpoint_or_nonTop_active_scaled :
    (j = 0 /\ Tube.gridScale delta N j = 1 /\
      kappa * (delta : ENNReal) ^ (3 * p.η m) <=
        normalizedQV5W58
          (Tube.gridScale delta N b / Tube.gridScale delta N j) active) \/
    (0 < j /\ QuotientScaledActiveQBandV5W58 delta
      (Tube.gridScale delta N b / Tube.gridScale delta N j)
      active kappa 1 (3 * p.η m))

theorem eventually_exists_stoppedTwoSource_of_preSecond_v5_w58
    [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero : Real} {p : Params} (hp : p.Spec beta gammaZero)
    (Cd : NNReal) (hCd : 1 <= Cd) (Kd cd : Nat) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall {iota : Type u} [DecidableEq iota]
        {sPrime : Finset iota} {V : iota -> ShadedTube delta E}
        (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
          (Tube.ssfGridLen delta) Cd)
        (a b m : Nat)
        (pre : PreSecondFactorLevelBPacketV5W58 (b := b) p U),
        StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
        Nonempty (StoppedTwoSourceV5W58
          (a := a) (b := b) p m U pre) := by
  classical
  let A : ENNReal :=
    ((Tube.volume_le.C 3 / Tube.le_volume.c 3 : NNReal) : ENNReal)
  have hA0 : A ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr
      (div_ne_zero (Tube.volume_le.C_pos 3).ne'
        (Tube.le_volume.c_pos 3).ne')
  have hAtop : A ≠ ⊤ := ENNReal.coe_ne_top
  have hbudget :=
    Kakeya.ml1Boot.WeakCoarseFibreCore.eventually_exists_completeOldFibreFreshCore_at_active_weak_w48.{u, v}
        (E := E) (p := p) (epsPrime := p.ε / 2) hdim
        (div_pos hp.epsPos (by norm_num))
        Cd hCd Kd cd
  have hfundAll :=
    (Filter.eventually_all_finset (Finset.range (p.N + 1))).2 (fun m hm => by
      have hmLt : m < p.N + 1 := Finset.mem_range.mp hm
      have hmN : m ≤ p.N := by omega
      have heta : 0 < p.η m :=
        hp.etaZeroPos.trans_le
          (hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
            (Set.mem_Iic.mpr hmN) (Nat.zero_le _))
      exact
        (Kakeya.ml1Boot.WeakCoarseFibreCore.eventually_exists_completeOldFibreFreshCore_at_active_weak_w48.{u, v}
            (E := E) (p := p) (epsPrime := p.η m / 8) hdim
            (div_pos heta (by norm_num))
            Cd hCd Kd cd).and
          ((Kakeya.ml1Boot.eventually_endpoint_exact_q0_lower_w47
            heta hA0 hAtop).and
            (Kakeya.ml1Boot.W48ReverseQBand.eventually_exists_firstProtectedCrossing_with_symmetric_QBand_or_top.{u, v}
                (E := E) heta)))
  filter_upwards [hbudget, hfundAll, self_mem_nhdsWithin,
      eventually_le_one_nhdsGT]
    with delta hbudgetDelta hfundDelta hdelta0 hdelta1
  intro iota _ sPrime V U a b m pre hblock
  have hmRange : m ∈ Finset.range (p.N + 1) := by
    simp only [Finset.mem_range]
    exact hblock.exponent_lt.trans_le (Nat.le_succ p.N)
  obtain ⟨hsourceEtaDelta, hq0Delta, hreverseDelta⟩ := hfundDelta m hmRange
  have hsPrime : sPrime.Nonempty := by
    exact pre.first_factor.sel_nonempty.mono (fun i hi =>
      (Finset.mem_filter.mp hi).1)
  have hnodes : ∀ k ∈ U.cover.indexSet b,
      ∃ i ∈ sPrime, U.cover.assign b i = k := by
    intro k hk
    exact Kakeya.ml1Boot.b3_raw_nodes_carry_leaf U hblock.fine_le hsPrime k hk
  obtain ⟨pTheta, hparentsOld⟩ :=
    Kakeya.ml1Boot.WeakCoarseFibreCore.exists_weakCoarseNodeParents U
      hblock.coarse_lt_fine.le hblock.fine_le hnodes
  have hparents : WeakCoarseNodeParentsV5W58 U a b pTheta :=
    { le_index := hparentsOld.le_index
      le_gridLen := hparentsOld.le_gridLen
      nodes_carry_leaf := hparentsOld.nodes_carry_leaf
      assign_comp := hparentsOld.assign_comp
      mapsTo := hparentsOld.mapsTo
      le_parent := hparentsOld.le_parent }
  have hmidMass : 0 < ∑ k ∈ pre.mid, volume (pre.ZTau k).shade := by
    obtain ⟨k, hk⟩ := pre.mid_nonempty
    have hcarrier : 0 < volume (pre.ZTau k).carrier :=
      (tube_volume_pos_ne_top
        (Tube.gridScale_pos hdelta0 (Tube.ssfGridLen delta) b)
        (pre.ZTau k).toTube).1
    have hhalf : 0 < (((2 : NNReal) : ENNReal)⁻¹) := by
      exact ENNReal.inv_pos.mpr (by norm_num)
    have hlower : 0 <
        ((2 : NNReal) : ENNReal)⁻¹ * (pre.mu0 : ENNReal) *
          volume (pre.ZTau k).carrier := by
      exact ENNReal.mul_pos
        (mul_ne_zero (ne_of_gt hhalf)
          (ne_of_gt (ENNReal.coe_pos.mpr pre.mu0_pos)))
        (ne_of_gt hcarrier)
    have hshade : 0 < volume (pre.ZTau k).shade :=
      lt_of_lt_of_le hlower (pre.density_band k hk).1
    exact hshade.trans_le
      (Finset.single_le_sum (fun i _ =>
        show (0 : ENNReal) ≤ volume (pre.ZTau i).shade from bot_le) hk)
  obtain ⟨q, hq, hactiveNe, hactiveMass, hmax⟩ :=
    Kakeya.ml1Boot.exists_positive_maxMultiplicity_tauAncestorClass_w48
      U pre.mid_nonempty hmidMass
  have hmidNodes : pre.mid ⊆ U.cover.indexSet b :=
    pre.mid_subset.trans
      (pre.first_factor.parent_subset.trans pre.tau_subset)
  obtain ⟨_jBudget, _pBudget, hbudgetPacket⟩ :=
    hbudgetDelta V U a b m pTheta hblock hparentsOld hsPrime
      hmidNodes hq
  dsimp only at hbudgetPacket
  rcases hbudgetPacket with
    ⟨_hactiveNeBudget, hactiveComplete, hcompleteNe,
      hcompleteNodes, hcompleteOld, _hjBudget, _hpBudget,
      _hcompleteFreshBudget, _hcrossBudget, hcompleteFrost,
      _hcompleteFreshFrostBudget, _hQBudget, _hQUpperBudget⟩
  obtain ⟨_jEta, _pEta, hetaPacket⟩ :=
    hsourceEtaDelta V U a b m pTheta hblock hparentsOld hsPrime
      hmidNodes hq
  dsimp only at hetaPacket
  rcases hetaPacket with
    ⟨_hactiveNeEta, _hactiveCompleteEta, _hcompleteNeEta,
      _hcompleteNodesEta, _hcompleteOldEta, _hjEta, _hpEta,
      _hcompleteFreshEta, _hcrossEta, hcompleteFrostEta,
      _hcompleteFreshFrostEta, _hQEta, _hQUpperEta⟩
  let active : Finset iota :=
    Kakeya.WangZahl.tauAncestorClass U b a pre.mid q
  let complete : Finset iota := fibre (U.cover.indexSet b) pTheta q
  have hactiveMid : active ⊆ pre.mid := by
    intro k hk
    exact (Kakeya.WangZahl.mem_tauAncestorClass U b a pre.mid q k).mp hk |>.1
  have hmN : m ≤ p.N := hblock.exponent_lt.le
  have heta : 0 < p.η m :=
    hp.etaZeroPos.trans_le
      (hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
        (Set.mem_Iic.mpr hmN) (Nat.zero_le _))
  have hcompleteFrostBudget :
      frostmanConstIn complete
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody ≤
        completeLevelAFrostmanBudgetV5W58 delta
          (Tube.ssfGridLen delta) a b m p := by
    simpa [complete, completeLevelAFrostmanBudgetV5W58,
      show -2 * (p.ε / 2) = -p.ε by ring] using hcompleteFrost
  have htau0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    Tube.gridScale_pos hdelta0 _ _
  have htau1 : Tube.gridScale delta (Tube.ssfGridLen delta) b ≤ 1 :=
    Tube.gridScale_le_one hdelta1 _ _
  have htheta0 : 0 < Tube.gridScale delta (Tube.ssfGridLen delta) a :=
    Tube.gridScale_pos hdelta0 _ _
  have hcontain : ∀ k ∈ complete,
      (U.cover.tube b k).toConvexSpaceBody ≤
        (U.cover.tube a q).toConvexSpaceBody := by
    intro k hk
    obtain ⟨hkb, hkq⟩ := Finset.mem_filter.mp hk
    have hle := hparentsOld.le_parent k hkb
    rwa [hkq] at hle
  have hq0Raw :
      (A * (delta : ENNReal) ^ (-2 * (p.η m / 8)))⁻¹ *
          ((Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) :
              ENNReal) ^ p.η m ≤
        normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a) complete := by
    simpa [A, complete, normalizedQV5W58] using
      Kakeya.ml1Boot.W47EndpointLowCard.completeFibre_normalizedQ_lower_of_frostman
        hdim hdelta0 htau0 htau1 htheta0 hcompleteNe
          (U.cover.tube b) (U.cover.tube a q) hcontain hcompleteFrostEta
  have hNpos : 0 < Tube.ssfGridLen delta :=
    (lt_of_lt_of_le (Nat.zero_lt_succ a) hblock.coarse_lt_fine).trans_le
      hblock.fine_le
  have hdeltaTau : delta ≤
      Tube.gridScale delta (Tube.ssfGridLen delta) b := by
    calc
      delta = Tube.gridScale delta (Tube.ssfGridLen delta)
          (Tube.ssfGridLen delta) := (Tube.gridScale_self delta hNpos).symm
      _ ≤ Tube.gridScale delta (Tube.ssfGridLen delta) b :=
        Tube.gridScale_antitone hdelta0 hdelta1 _ hblock.fine_le
  have htauTheta : Tube.gridScale delta (Tube.ssfGridLen delta) b ≤
      Tube.gridScale delta (Tube.ssfGridLen delta) a :=
    Tube.gridScale_antitone hdelta0 hdelta1 _ hblock.coarse_lt_fine.le
  have htheta1 : Tube.gridScale delta (Tube.ssfGridLen delta) a ≤ 1 :=
    Tube.gridScale_le_one hdelta1 _ _
  have hratioLower : delta ≤
      Tube.gridScale delta (Tube.ssfGridLen delta) b /
        Tube.gridScale delta (Tube.ssfGridLen delta) a :=
    Kakeya.WangZahl.scale_le_ratio_of_le_of_le_one
      htheta0 hdeltaTau htheta1
  have hratioUpper :
      Tube.gridScale delta (Tube.ssfGridLen delta) b /
        Tube.gridScale delta (Tube.ssfGridLen delta) a ≤ 1 :=
    (div_le_one htheta0).mpr htauTheta
  have hq0Funded :
      (delta : ENNReal) ^ (2 * p.η m) ≤
        (A * (delta : ENNReal) ^ (-2 * (p.η m / 8)))⁻¹ *
          ((Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) :
              ENNReal) ^ p.η m := by
    simpa [show -2 * (p.η m / 8) = -(p.η m / 4) by ring] using
      hq0Delta hratioLower hratioUpper
  have hdeltaE1 : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdelta1
  have hterminal : (delta : ENNReal) ^ (3 * p.η m) ≤
      normalizedQV5W58
        (Tube.gridScale delta (Tube.ssfGridLen delta) b /
          Tube.gridScale delta (Tube.ssfGridLen delta) a) complete := by
    calc
      (delta : ENNReal) ^ (3 * p.η m) ≤
          (delta : ENNReal) ^ (2 * p.η m) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by linarith)
      _ ≤ (A * (delta : ENNReal) ^ (-2 * (p.η m / 8)))⁻¹ *
          ((Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a : NNReal) :
              ENNReal) ^ p.η m := hq0Funded
      _ ≤ normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a) complete := hq0Raw
  obtain ⟨j, pJ, hj, hcross, hpJ, hcompleteFresh, hQlow, hstopBand⟩ :=
    hreverseDelta U hsPrime hblock.coarse_lt_fine.le hblock.fine_le
      (tauNodes := U.cover.indexSet b) (source := complete) le_rfl hcompleteNe
      (pSigma := q) (by simpa [complete] using hcompleteOld)
      (by simpa [normalizedQV5W58] using hterminal)
  have hactiveNe' : active.Nonempty := by
    simpa [active] using hactiveNe
  have hcompleteNe' : complete.Nonempty := by
    simpa [complete] using hcompleteNe
  have hactiveComplete' : active ⊆ complete := by
    simpa [active, complete] using hactiveComplete
  have hcompleteNodes' : complete ⊆ U.cover.indexSet b := by
    simpa [complete] using hcompleteNodes
  have hactiveMid' : active ⊆ pre.mid := hactiveMid
  have hcompleteConstant : ∀ k, k ∈ complete ->
      U.nodeAncestor b j k = pJ := by
    intro k hk
    have hkclass : k ∈ Kakeya.WangZahl.tauAncestorClass U b j complete pJ := by
      rw [hcompleteFresh]
      exact hk
    exact
      (Kakeya.WangZahl.mem_tauAncestorClass U b j complete pJ k).mp hkclass |>.2
  have hactiveConstant : ∀ k, k ∈ active ->
      U.nodeAncestor b j k = pJ := by
    intro k hk
    exact hcompleteConstant k (hactiveComplete' hk)
  have hactiveFresh :
      Kakeya.WangZahl.tauAncestorClass U b j active pJ = active :=
    Kakeya.WangZahl.tauAncestorClass_eq_of_constant_ancestor U hactiveConstant
  have haN : a ≤ Tube.ssfGridLen delta :=
    hblock.coarse_lt_fine.le.trans hblock.fine_le
  have hqA : q ∈ U.cover.indexSet a :=
    Kakeya.WangZahl.activeRhoParents_subset_indexSet U hsPrime
      haN hblock.fine_le hmidNodes hq
  have hpJMem : pJ ∈ U.cover.indexSet j := by
    rw [hpJ]
    exact U.nodeAncestor_mem (hj.trans haN) haN hsPrime hqA
  let kappa : ENNReal := retainedShareV5W58 active complete
  have hactiveCard0 : (active.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hactiveNe'
  have hcompleteCard0 : (complete.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hcompleteNe'
  have hactiveCardTop : (active.card : ENNReal) ≠ ⊤ := by simp
  have hcompleteCardTop : (complete.card : ENNReal) ≠ ⊤ := by simp
  have hkappa0 : kappa ≠ 0 := by
    dsimp [kappa, retainedShareV5W58]
    exact ENNReal.div_ne_zero.mpr ⟨hactiveCard0, hcompleteCardTop⟩
  have hkappaTop : kappa ≠ ⊤ := by
    dsimp [kappa, retainedShareV5W58]
    exact ENNReal.div_ne_top hactiveCardTop hcompleteCard0
  have hkappaOne : kappa ≤ 1 := by
    dsimp [kappa, retainedShareV5W58]
    rw [ENNReal.div_le_iff_le_mul (Or.inl hcompleteCard0)
      (Or.inl hcompleteCardTop), one_mul]
    exact_mod_cast Finset.card_le_card hactiveComplete'
  have hcardShare :
      kappa * (complete.card : ENNReal) = (active.card : ENNReal) := by
    dsimp [kappa, retainedShareV5W58]
    exact ENNReal.div_mul_cancel hcompleteCard0 hcompleteCardTop
  have hvol : ∀ k ∈ complete,
      volume (U.cover.tube b k).carrier =
        volume (U.cover.tube b hcompleteNe'.choose).carrier := by
    intro k _hk
    exact Tube.volume_carrier_eq_volume_carrier
      (U.cover.tube b k) (U.cover.tube b hcompleteNe'.choose)
  have hactiveFrost :
      frostmanConstIn active
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody ≤
        kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta
          (Tube.ssfGridLen delta) a b m p := by
    calc
      frostmanConstIn active
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody ≤
        kappa⁻¹ * frostmanConstIn complete
          (fun k => (U.cover.tube b k).toConvexSpaceBody)
          (U.cover.tube a q).toConvexSpaceBody :=
        ConvexSpaceBody.frostmanConstIn_subfamily_le
          hcompleteNe' hvol hcontain hactiveComplete' hkappa0 hcardShare.le
      _ ≤ kappa⁻¹ * completeLevelAFrostmanBudgetV5W58 delta
          (Tube.ssfGridLen delta) a b m p := by gcongr
  have hQidentity (r : NNReal) :
      normalizedQV5W58 r active =
        kappa * normalizedQV5W58 r complete := by
    dsimp [normalizedQV5W58]
    rw [← hcardShare]
    ring
  have hactiveTerminal :
      kappa * (delta : ENNReal) ^ (3 * p.η m) ≤
        normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a) active := by
    calc
      kappa * (delta : ENNReal) ^ (3 * p.η m) ≤
          kappa * normalizedQV5W58
            (Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) a) complete := by
        gcongr
      _ = normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) a) active :=
        (hQidentity _).symm
  have hcompleteStopLower :
      (delta : ENNReal) ^ (3 * p.η m) ≤
        normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) j) complete := by
    simpa [normalizedQV5W58, hcompleteFresh] using hQlow
  have hactiveStopLower :
      kappa * (delta : ENNReal) ^ (3 * p.η m) ≤
        normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) j) active := by
    calc
      kappa * (delta : ENNReal) ^ (3 * p.η m) ≤
          kappa * normalizedQV5W58
            (Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) j) complete := by
        gcongr
      _ = normalizedQV5W58
          (Tube.gridScale delta (Tube.ssfGridLen delta) b /
            Tube.gridScale delta (Tube.ssfGridLen delta) j) active :=
        (hQidentity _).symm
  have hstopBand' := hstopBand
  have hcompleteEndpoint :
      (j = 0 ∧ Tube.gridScale delta (Tube.ssfGridLen delta) j = 1 ∧
        (delta : ENNReal) ^ (3 * p.η m) ≤
          normalizedQV5W58
            (Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) j) complete) ∨
      (0 < j ∧ SymmetricCompleteQBandV5W58 delta
        (Tube.gridScale delta (Tube.ssfGridLen delta) b /
          Tube.gridScale delta (Tube.ssfGridLen delta) j)
        complete 1 (3 * p.η m)) := by
    rcases hstopBand with hzero | hnon
    · exact Or.inl ⟨hzero.1, hzero.2, hcompleteStopLower⟩
    · right
      refine ⟨hnon.1, ?_⟩
      constructor
      · simpa [SymmetricCompleteQBandV5W58] using hcompleteStopLower
      · simpa [normalizedQV5W58, hcompleteFresh] using hnon.2
  have hactiveEndpoint :
      (j = 0 ∧ Tube.gridScale delta (Tube.ssfGridLen delta) j = 1 ∧
        kappa * (delta : ENNReal) ^ (3 * p.η m) ≤
          normalizedQV5W58
            (Tube.gridScale delta (Tube.ssfGridLen delta) b /
              Tube.gridScale delta (Tube.ssfGridLen delta) j) active) ∨
      (0 < j ∧ QuotientScaledActiveQBandV5W58 delta
        (Tube.gridScale delta (Tube.ssfGridLen delta) b /
          Tube.gridScale delta (Tube.ssfGridLen delta) j)
        active kappa 1 (3 * p.η m)) := by
    rcases hstopBand' with hzero | hnon
    · exact Or.inl ⟨hzero.1, hzero.2, hactiveStopLower⟩
    · right
      refine ⟨hnon.1, ?_⟩
      constructor
      · simpa [QuotientScaledActiveQBandV5W58] using hactiveStopLower
      · calc
          normalizedQV5W58
              (Tube.gridScale delta (Tube.ssfGridLen delta) b /
                Tube.gridScale delta (Tube.ssfGridLen delta) j) active =
            kappa * normalizedQV5W58
              (Tube.gridScale delta (Tube.ssfGridLen delta) b /
                Tube.gridScale delta (Tube.ssfGridLen delta) j) complete :=
            hQidentity _
          _ ≤ kappa * ((1 : ENNReal) *
              (delta : ENNReal) ^ (-(3 * p.η m))) := by
            gcongr
            simpa [normalizedQV5W58, hcompleteFresh] using hnon.2
  exact Nonempty.intro
    { pTheta := pTheta
      parents := hparents
      q := q
      active := active
      complete := complete
      j := j
      pJ := pJ
      q_active := hq
      active_eq := by rfl
      complete_eq := by simpa [complete, completeClassV5W58] using hcompleteOld
      complete_fibre_eq := by rfl
      active_nonempty := hactiveNe'
      complete_nonempty := hcompleteNe'
      active_subset_complete := hactiveComplete'
      active_subset_mid := hactiveMid'
      complete_subset_levelB := hcompleteNodes'
      active_mass_pos := by simpa [active] using hactiveMass
      max_multiplicity_paid := by simpa [active] using hmax
      kappa := kappa
      kappa_eq := by rfl
      kappa_ne_zero := hkappa0
      kappa_ne_top := hkappaTop
      kappa_le_one := hkappaOne
      card_share_exact := hcardShare
      level_le := hj
      stopped_parent_eq := hpJ
      stopped_parent_mem := hpJMem
      complete_constant_at_stop := hcompleteConstant
      active_constant_at_stop := hactiveConstant
      complete_eq_stopped_class := hcompleteFresh
      active_eq_stopped_class := hactiveFresh
      first_crossing_complete := hcross
      frostman_complete_levelA := hcompleteFrostBudget
      frostman_active_levelA := hactiveFrost
      complete_Q_lower_at_a := hterminal
      active_Q_lower_at_a_scaled := hactiveTerminal
      Q_identity_at_a := hQidentity _
      Q_identity_at_stop := hQidentity _
      endpoint_or_nonTop_complete := hcompleteEndpoint
      endpoint_or_nonTop_active_scaled := hactiveEndpoint }

end
end Kakeya.ml1Boot.W58QuotientAwareQV5
