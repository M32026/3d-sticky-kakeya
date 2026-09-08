module

public import Kakeya.DimensionThree.MainLemma1.UpstreamMiddlePaymentsW50
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50UpstreamMiddlePayments

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

local instance : DecidableEq (ConvexSpaceBody E) := Classical.decEq _

/-- A same-scale shading refinement retains its mass-weighted cardinal share. -/
theorem card_share_of_tube_refinement_upstream_w50
    [Nontrivial E]
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} {s sf : Finset iota}
    (T Z : iota -> ShadedTube delta E) {c : NNReal}
    (hs : s.Nonempty) (hZ : ∀ i, (Z i).toTube = (T i).toTube)
    (href : ShadedBody.IsCRefinement sf (fun i => (Z i).toShadedBody) s
      (fun i => (T i).toShadedBody) c) :
    ((c : ENNReal) * ShadedBody.fullness s (fun i => (T i).toShadedBody)) *
        (s.card : ENNReal) <= (sf.card : ENNReal) := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  let vol0 : ENNReal := volume (T i0).carrier
  have hvol0 : vol0 ≠ 0 := by
    simpa [vol0] using
      (Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T i0).toTube).1.ne'
  have hvolTop : vol0 ≠ ⊤ := by
    simpa [vol0] using
      (Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T i0).toTube).2.ne
  have hsame : ∀ i, volume (T i).carrier = vol0 := by
    intro i
    simpa [vol0] using
      Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i0).toTube
  have hlow : ∀ i ∈ s, vol0 <= volume ((T i).toShadedBody).carrier := by
    intro i hi
    exact le_of_eq (hsame i).symm
  have hupp : ∀ i ∈ sf, volume ((Z i).toShadedBody).shade <= vol0 := by
    intro i hi
    calc
      volume (Z i).shade <= volume (Z i).carrier :=
        measure_mono (Z i).shade_subset
      _ = volume (T i).carrier := by
        exact congrArg (fun W : Tube delta E => volume W.carrier) (hZ i)
      _ = vol0 := hsame i
  have hcard := card_le_of_cRefinement_of_fullness
    (s := s) (s' := sf) (V := fun i => (T i).toShadedBody)
    (V' := fun i => (Z i).toShadedBody) (c := c)
    (lam := ShadedBody.fullness s (fun i => (T i).toShadedBody))
    (v := vol0) hvol0 hvolTop href le_rfl hlow hupp
  exact_mod_cast hcard

/-- A same-scale shade-mass retention gives its corresponding cardinal share. -/
theorem card_share_of_mass_retention_upstream_w50
    [Nontrivial E]
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} {s active : Finset iota}
    (T Z : iota -> ShadedTube delta E) (hs : s.Nonempty) {c : ENNReal}
    (hmass : c * (∑ i ∈ s, volume (T i).shade) <=
      ∑ i ∈ active, volume (Z i).shade) :
    (c * ShadedBody.fullness s (fun i => (T i).toShadedBody)) *
        (s.card : ENNReal) <= (active.card : ENNReal) := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  let vol0 : ENNReal := volume (T i0).carrier
  have hvol0 : vol0 ≠ 0 := by
    simpa [vol0] using
      (Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T i0).toTube).1.ne'
  have hvolTop : vol0 ≠ ⊤ := by
    simpa [vol0] using
      (Tube.volume_pos_and_lt_top hdelta0 hdelta1 (T i0).toTube).2.ne
  have hlow : ∀ i ∈ s, vol0 <= volume ((T i).toShadedBody).carrier := by
    intro i hi
    exact le_of_eq (by
      simpa [vol0] using
        Tube.volume_carrier_eq_volume_carrier (T i0).toTube (T i).toTube)
  have hupp : ∀ i ∈ active,
      volume ((Z i).toShadedBody).shade <= vol0 := by
    intro i hi
    calc
      volume (Z i).shade <= volume (Z i).carrier :=
        measure_mono (Z i).shade_subset
      _ = vol0 := by
        simpa [vol0] using
          Tube.volume_carrier_eq_volume_carrier (Z i).toTube (T i0).toTube
  apply (ENNReal.mul_le_mul_iff_left hvol0 hvolTop).mp
  calc
    (c * ShadedBody.fullness s (fun i => (T i).toShadedBody)) *
          (s.card : ENNReal) * vol0 =
        c * ((ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) *
          ((s.card : ENNReal) * vol0)) := by ring
    _ <= c * ∑ i ∈ s, volume (T i).shade := by
      gcongr
      exact ShadedBody.coe_fullness_mul_le_sum_volume_shade s
        (fun i => (T i).toShadedBody) le_rfl hlow
    _ <= ∑ i ∈ active, volume (Z i).shade := hmass
    _ <= (active.card : ENNReal) * vol0 := by
      simpa [mul_comm] using Finset.sum_le_sum hupp

omit [MeasurableSpace E] [BorelSpace E] in
/-- A retained leaf share forces the corresponding raw active hierarchy level
to retain the same share, up to the uniformity square. -/
theorem activeParents_card_share_of_uniform_upstream_w50
    [Nontrivial E]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s sf active : Finset iota} (T : iota -> Tube delta E)
    {N b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hb : b <= N)
    (hactiveSub : active ⊆ U.cover.indexSet b)
    (hsf : sf ⊆ s) (hmaps : ∀ i ∈ sf, U.cover.assign b i ∈ active)
    (hactive : ∃ k ∈ active,
      (fibre sf (U.cover.assign b) k).Nonempty)
    {r : ENNReal} (hret : r * (s.card : ENNReal) <= (sf.card : ENNReal)) :
    r * ((U.cover.indexSet b).card : ENNReal) <=
      (C : ENNReal) ^ 2 * (active.card : ENNReal) := by
  classical
  let branch : ENNReal := (U.branchingN b : ENNReal)
  have hbranch0 : branch ≠ 0 := by
    obtain ⟨k, hk, i, hi⟩ := hactive
    have his : i ∈ s := hsf (Finset.mem_filter.mp hi).1
    have hik : U.cover.assign b i = k := (Finset.mem_filter.mp hi).2
    have hiclass : i ∈ Tube.coverClass s (U.cover.assign b) k := by
      simp [Tube.coverClass, his, hik]
    have hcardpos : (0 : NNReal) <
        ((Tube.coverClass s (U.cover.assign b) k).card : NNReal) := by
      exact_mod_cast Finset.card_pos.mpr ⟨i, hiclass⟩
    have hupp := U.card_class_le b hb k (hactiveSub hk)
    intro hzero
    have hbranchNat : U.branchingN b = 0 := by
      dsimp [branch] at hzero
      exact_mod_cast hzero
    rw [hbranchNat, mul_zero] at hupp
    exact (not_lt_of_ge hupp) hcardpos
  have hbranchTop : branch ≠ ⊤ := by
    dsimp [branch]
    exact ENNReal.coe_ne_top
  have hsum : (sf.card : ENNReal) =
      ∑ k ∈ active, ((fibre sf (U.cover.assign b) k).card : ENNReal) := by
    have hnat : sf.card =
        ∑ k ∈ active, (fibre sf (U.cover.assign b) k).card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast hnat
  have hsfUpper : (sf.card : ENNReal) <=
      (active.card : ENNReal) * ((C : ENNReal) * branch) := by
    calc
      (sf.card : ENNReal) =
          ∑ k ∈ active, ((fibre sf (U.cover.assign b) k).card : ENNReal) := hsum
      _ <= ∑ _k ∈ active, (C : ENNReal) * branch := by
        apply Finset.sum_le_sum
        intro k hk
        have hsub : fibre sf (U.cover.assign b) k ⊆
            Tube.coverClass s (U.cover.assign b) k := by
          intro i hi
          simpa only [fibre, Tube.coverClass, Finset.mem_filter] using
            ⟨hsf (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
        have hcard : ((fibre sf (U.cover.assign b) k).card : ENNReal) <=
            ((Tube.coverClass s (U.cover.assign b) k).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hsub
        exact hcard.trans (by
          have h := ENNReal.coe_le_coe.mpr (U.card_class_le b hb k (hactiveSub hk))
          simpa [branch, ENNReal.coe_mul] using h)
      _ = (active.card : ENNReal) * ((C : ENNReal) * branch) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hlevel : branch * ((U.cover.indexSet b).card : ENNReal) <=
      (C : ENNReal) * (s.card : ENNReal) := by
    have h := ENNReal.coe_le_coe.mpr (branchingN_mul_card_indexSet_le U hb)
    simpa [branch, ENNReal.coe_mul] using h
  apply (ENNReal.mul_le_mul_iff_right hbranch0 hbranchTop).mp
  calc
    branch * (r * ((U.cover.indexSet b).card : ENNReal)) =
        r * (branch * ((U.cover.indexSet b).card : ENNReal)) := by ring
    _ <= r * ((C : ENNReal) * (s.card : ENNReal)) := by gcongr
    _ = (C : ENNReal) * (r * (s.card : ENNReal)) := by ring
    _ <= (C : ENNReal) * (sf.card : ENNReal) := by gcongr
    _ <= (C : ENNReal) *
        ((active.card : ENNReal) * ((C : ENNReal) * branch)) := by gcongr
    _ = branch * ((C : ENNReal) ^ 2 * (active.card : ENNReal)) := by ring

/-- A level body class has at most `C` raw nodes. -/
theorem card_bodyClass_le_upstream_w50 [Nontrivial E]
    {iota : Type u} [DecidableEq iota] {delta : NNReal}
    {s : Finset iota} {T : iota -> Tube delta E} {N k : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hk : k <= N) (hs : s.Nonempty)
    (q : iota) :
    (((U.cover.indexSet k).filter fun j =>
      (U.cover.tube k j).toConvexSpaceBody =
        (U.cover.tube k q).toConvexSpaceBody).card : NNReal) <= C := by
  classical
  apply le_trans (show
      (((U.cover.indexSet k).filter fun j =>
        (U.cover.tube k j).toConvexSpaceBody =
          (U.cover.tube k q).toConvexSpaceBody).card : NNReal) <=
        (U.meetingNodes k (U.cover.tube k q)).card by
      exact_mod_cast Finset.card_le_card (by
        intro j hj
        rw [Finset.mem_filter] at hj
        obtain ⟨i, hi, hassign⟩ :=
          W50Upstream.raw_nodes_carry_leaf_upstream_w50 U hk hs j hj.1
        simp only [Tube.UniformTubeSet.meetingNodes, Finset.mem_filter]
        refine ⟨hj.1, i, hi, ?_, ?_⟩
        · simpa [hassign] using U.cover.le_tube_assign k hk i hi
        · simpa [hassign, hj.2] using U.cover.le_tube_assign k hk i hi))
  exact U.card_meetingNodes_le hk (U.cover.tube k q)

/-- A counted representative has at most `C` raw nodes over each active value. -/
theorem card_rawNodes_over_active_reps_le_upstream_w50 [Nontrivial E]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> Tube delta E} {N b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hb : b <= N) (hs : s.Nonempty)
    {t active : Finset iota} {rep : iota -> iota}
    (ht : t ⊆ U.cover.indexSet b) (hactive : active ⊆ t)
    (hrep : ∀ j ∈ U.cover.indexSet b,
      rep j ∈ t /\
        (U.cover.tube b (rep j)).toConvexSpaceBody =
          (U.cover.tube b j).toConvexSpaceBody) :
    (((U.cover.indexSet b).filter fun j => rep j ∈ active).card : ENNReal) <=
      (C : ENNReal) * (active.card : ENNReal) := by
  classical
  let rawActive : Finset iota :=
    (U.cover.indexSet b).filter fun j => rep j ∈ active
  have hmaps : ∀ j ∈ rawActive, rep j ∈ active := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hsum : (rawActive.card : ENNReal) =
      ∑ q ∈ active, ((fibre rawActive rep q).card : ENNReal) := by
    have hnat : rawActive.card =
        ∑ q ∈ active, (fibre rawActive rep q).card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast hnat
  have hfibre : ∀ q ∈ active,
      ((fibre rawActive rep q).card : ENNReal) <= (C : ENNReal) := by
    intro q hq
    have hqfull : q ∈ U.cover.indexSet b := ht (hactive hq)
    have hsub : fibre rawActive rep q ⊆
        (U.cover.indexSet b).filter (fun j =>
          (U.cover.tube b j).toConvexSpaceBody =
            (U.cover.tube b q).toConvexSpaceBody) := by
      intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjraw := (Finset.mem_filter.mp hj'.1).1
      have hjbody := (hrep j hjraw).2
      exact Finset.mem_filter.mpr ⟨hjraw, by
        simpa [hj'.2] using hjbody.symm⟩
    have hcard : (fibre rawActive rep q).card <=
        ((U.cover.indexSet b).filter (fun j =>
          (U.cover.tube b j).toConvexSpaceBody =
            (U.cover.tube b q).toConvexSpaceBody)).card :=
      Finset.card_le_card hsub
    have hclass := card_bodyClass_le_upstream_w50 U hb hs q
    have hcardE : ((fibre rawActive rep q).card : ENNReal) <=
        (((U.cover.indexSet b).filter (fun j =>
          (U.cover.tube b j).toConvexSpaceBody =
            (U.cover.tube b q).toConvexSpaceBody)).card : ENNReal) := by
      exact_mod_cast hcard
    have hclassE :
        ((((U.cover.indexSet b).filter (fun j =>
          (U.cover.tube b j).toConvexSpaceBody =
            (U.cover.tube b q).toConvexSpaceBody)).card : NNReal) : ENNReal) <=
          (C : ENNReal) := ENNReal.coe_le_coe.mpr hclass
    exact hcardE.trans (by simpa using hclassE)
  calc
    (((U.cover.indexSet b).filter fun j => rep j ∈ active).card : ENNReal) =
        (rawActive.card : ENNReal) := by rfl
    _ = ∑ q ∈ active, ((fibre rawActive rep q).card : ENNReal) := hsum
    _ <= ∑ _q ∈ active, (C : ENNReal) := by
      exact Finset.sum_le_sum fun q hq => hfibre q hq
    _ = (C : ENNReal) * (active.card : ENNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [mul_comm]

#print axioms card_share_of_tube_refinement_upstream_w50
#print axioms card_share_of_mass_retention_upstream_w50
#print axioms activeParents_card_share_of_uniform_upstream_w50
#print axioms card_bodyClass_le_upstream_w50
#print axioms card_rawNodes_over_active_reps_le_upstream_w50

end
end Kakeya.ml1Boot.W50UpstreamMiddlePayments
