module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.CanonicalMiddleUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.W45H5Consumer

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50ExactCountedMiddle

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-! The first bridge is purely structural.  It upgrades the counted canonical map
`pTheta0` to the representative-valued map used by the actual product packet. -/

omit [MeasurableSpace E] [BorelSpace E] in
theorem representative_parent_family_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hab : a <= b) (hb : b <= N)
    {tTheta : Finset iota} {pTheta0 repTheta : iota -> iota}
    (htTheta : tTheta ⊆ U.cover.indexSet a)
    (hpTheta0 : ∀ k ∈ U.cover.indexSet b, pTheta0 k ∈ U.cover.indexSet a)
    (hleTheta0 : ∀ k ∈ U.cover.indexSet b,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a (pTheta0 k)).toConvexSpaceBody)
    (hrepTheta : ∀ l ∈ U.cover.indexSet a,
      repTheta l ∈ tTheta ∧
        (U.cover.tube a (repTheta l)).toConvexSpaceBody =
          (U.cover.tube a l).toConvexSpaceBody)
    (hparentTheta : IsParentFamily (U.cover.indexSet b) (U.cover.tube b) tTheta
      (U.cover.tube a) (fun k => repTheta (pTheta0 k))) :
    IsParentFamily (U.cover.indexSet b) (U.cover.tube b) tTheta
      (U.cover.tube a) (fun k => repTheta (pTheta0 k)) := by
  exact hparentTheta

omit [MeasurableSpace E] [BorelSpace E] in
theorem representative_parent_family_of_counted_fields_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C)
    {tTheta : Finset iota} {pTheta0 repTheta : iota -> iota}
    (htTheta : tTheta ⊆ U.cover.indexSet a)
    (hpTheta0 : ∀ k ∈ U.cover.indexSet b, pTheta0 k ∈ U.cover.indexSet a)
    (hleTheta0 : ∀ k ∈ U.cover.indexSet b,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a (pTheta0 k)).toConvexSpaceBody)
    (hrepTheta : ∀ l ∈ U.cover.indexSet a,
      repTheta l ∈ tTheta ∧
        (U.cover.tube a (repTheta l)).toConvexSpaceBody =
          (U.cover.tube a l).toConvexSpaceBody)
    (hinj : Set.InjOn (fun l => (U.cover.tube a l).toConvexSpaceBody)
      (tTheta : Set iota)) :
    IsParentFamily (U.cover.indexSet b) (U.cover.tube b) tTheta
      (U.cover.tube a) (fun k => repTheta (pTheta0 k)) := by
  refine { mapsTo := ?_, injOn := hinj, le_parent := ?_ }
  · intro k hk
    exact (hrepTheta (pTheta0 k) (hpTheta0 k hk)).1
  · intro k hk
    have hk0 := hpTheta0 k hk
    have hle := hleTheta0 k hk
    have hbody := (hrepTheta (pTheta0 k) hk0).2
    exact hle.trans_eq hbody.symm

/-! The representative map has a useful extra property which is not present for an
arbitrary total map: it is the identity on its selected carrier.  This lets us
read a level-a assignment class through the representative-valued parent map. -/

omit [MeasurableSpace E] [BorelSpace E] in
theorem representative_self_on_carrier_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> Tube delta E} {N a : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C)
    {tTheta : Finset iota} {repTheta : iota -> iota}
    (htTheta : tTheta ⊆ U.cover.indexSet a)
    (hrepTheta : ∀ l ∈ U.cover.indexSet a,
      repTheta l ∈ tTheta ∧
        (U.cover.tube a (repTheta l)).toConvexSpaceBody =
          (U.cover.tube a l).toConvexSpaceBody)
    (hinj : Set.InjOn (fun l => (U.cover.tube a l).toConvexSpaceBody)
      (tTheta : Set iota)) :
    ∀ l ∈ tTheta, repTheta l = l := by
  intro l hl
  have hlA : l ∈ U.cover.indexSet a := htTheta hl
  have hrep := hrepTheta l hlA
  exact hinj hrep.1 hl hrep.2

/-! A counted representative parent still has the same `C^5` complete-fibre
comparison as the canonical assignment parent.  The proof is deliberately
written against the counted fields (`pTheta0`, `repTheta`, and the leaf
assignment identity), so it applies before any Case-Two consumer is imported. -/

set_option maxHeartbeats 12000000 in
theorem representative_complete_fibre_card_band_w50 [Nontrivial E]
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> Tube delta E)
    {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C)
    (hab : a <= b) (hb : b <= N) (hs : s.Nonempty)
    {tTheta : Finset iota} {pTheta0 repTheta : iota -> iota}
    (htTheta : tTheta ⊆ U.cover.indexSet a)
    (hpTheta0 : ∀ k ∈ U.cover.indexSet b, pTheta0 k ∈ U.cover.indexSet a)
    (hleTheta0 : ∀ k ∈ U.cover.indexSet b,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a (pTheta0 k)).toConvexSpaceBody)
    (hcompTheta : ∀ i ∈ s,
      pTheta0 (U.cover.assign b i) = U.cover.assign a i)
    (hrepTheta : ∀ l ∈ U.cover.indexSet a,
      repTheta l ∈ tTheta ∧
        (U.cover.tube a (repTheta l)).toConvexSpaceBody =
          (U.cover.tube a l).toConvexSpaceBody)
    (hinj : Set.InjOn (fun l => (U.cover.tube a l).toConvexSpaceBody)
      (tTheta : Set iota))
    {l l' : iota} (hl : l ∈ tTheta) (hl' : l' ∈ tTheta) :
    ((fibre (U.cover.indexSet b)
        (fun k => repTheta (pTheta0 k)) l).card : ENNReal) <=
      (C : ENNReal) ^ 5 *
        ((fibre (U.cover.indexSet b)
          (fun k => repTheta (pTheta0 k)) l').card : ENNReal) := by
  classical
  let pbar : iota -> iota := fun k => repTheta (pTheta0 k)
  have hparent : IsParentFamily (U.cover.indexSet b) (U.cover.tube b)
      tTheta (U.cover.tube a) pbar :=
    representative_parent_family_of_counted_fields_w50 U htTheta hpTheta0
      hleTheta0 hrepTheta hinj
  have hrepId : ∀ q ∈ tTheta, repTheta q = q :=
    representative_self_on_carrier_w50 U htTheta hrepTheta hinj
  let F : Finset iota := fibre (U.cover.indexSet b) pbar l
  let F' : Finset iota := fibre (U.cover.indexSet b) pbar l'
  have hFsub : F ⊆ U.nodesIn b (U.cover.tube a l).toConvexSpaceBody := by
    intro k hk
    have hk' : k ∈ U.cover.indexSet b ∧ pbar k = l := by
      simpa [F, fibre, Finset.mem_filter] using hk
    have hle := hparent.le_parent k hk'.1
    rw [hk'.2] at hle
    exact (U.mem_nodesIn_iff b (U.cover.tube a l).toConvexSpaceBody k).2
      ⟨hk'.1, hle⟩
  let Nb : Real := (U.branchingN b : Real)
  let Na : Real := (U.branchingN a : Real)
  have hupper : Nb * (F.card : Real) <= (C : Real) ^ 3 * Na := by
    have hnodes := branching_mul_card_nodesIn_le U hab hb l
    have hnodesR : Nb *
        ((U.nodesIn b (U.cover.tube a l).toConvexSpaceBody).card : Real) <=
        (C : Real) ^ 3 * Na := by
      simpa [Nb, Na] using hnodes
    have hcard : (F.card : Real) <=
        ((U.nodesIn b (U.cover.tube a l).toConvexSpaceBody).card : Real) := by
      exact_mod_cast Finset.card_le_card hFsub
    calc
      Nb * (F.card : Real) <= Nb *
          ((U.nodesIn b (U.cover.tube a l).toConvexSpaceBody).card : Real) := by
        exact mul_le_mul_of_nonneg_left hcard (by positivity)
      _ <= (C : Real) ^ 3 * Na := hnodesR
  let classA : Finset iota :=
    Tube.coverClass s (U.cover.assign a) l'
  let cls : iota -> Finset iota :=
    fun k => Tube.coverClass s (U.cover.assign b) k
  have hclassA_sub : classA ⊆ F'.biUnion cls := by
    intro i hi
    have hi' : i ∈ s ∧ U.cover.assign a i = l' := by
      simpa [classA, Tube.coverClass] using hi
    let k : iota := U.cover.assign b i
    have hkB : k ∈ U.cover.indexSet b :=
      U.cover.assign_mem b hb i hi'.1
    have hp0 : pTheta0 k = l' := by
      dsimp [k]
      rw [hcompTheta i hi'.1, hi'.2]
    have hpk : pbar k = l' := by
      dsimp [pbar]
      rw [hp0, hrepId l' hl']
    have hkF' : k ∈ F' := by
      exact Finset.mem_filter.mpr ⟨hkB, hpk⟩
    have hiCls : i ∈ cls k := by
      dsimp [cls]
      simp [Tube.coverClass, hi'.1, k]
    exact Finset.mem_biUnion.mpr ⟨k, hkF', hiCls⟩
  have hclassA_card : (classA.card : Real) <=
      (F'.card : Real) * (C : Real) * Nb := by
    have hcardUnion : (F'.biUnion cls).card <=
        ∑ k ∈ F', (cls k).card := Finset.card_biUnion_le
    have hsubCard : classA.card <= (F'.biUnion cls).card :=
      Finset.card_le_card hclassA_sub
    have hsumR : ((∑ k ∈ F', (cls k).card : Nat) : Real) =
        ∑ k ∈ F', ((cls k).card : Real) := by
      simp
    have hsumBound : (∑ k ∈ F', ((cls k).card : Real)) <=
        (F'.card : Real) * (C : Real) * Nb := by
      calc
        (∑ k ∈ F', ((cls k).card : Real)) <=
            ∑ k ∈ F', ((C : Real) * Nb) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ∈ U.cover.indexSet b :=
            (Finset.mem_filter.mp hk).1
          exact_mod_cast U.card_class_le b hb k hk'
        _ = (F'.card : Real) * (C : Real) * Nb := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    calc
      (classA.card : Real) <= ((F'.biUnion cls).card : Real) := by
        exact_mod_cast hsubCard
      _ <= (∑ k ∈ F', (cls k).card : Nat) := by
        exact_mod_cast hcardUnion
      _ = ∑ k ∈ F', ((cls k).card : Real) := hsumR
      _ <= (F'.card : Real) * (C : Real) * Nb := hsumBound
  have hlower : Na <= (C : Real) ^ 2 * Nb * (F'.card : Real) := by
    have hclassLower : Na <= (C : Real) * (classA.card : Real) := by
      have h := U.le_card_class a (hab.trans hb) l' (htTheta hl')
      exact_mod_cast h
    calc
      Na <= (C : Real) * (classA.card : Real) := hclassLower
      _ <= (C : Real) * ((F'.card : Real) * (C : Real) * Nb) := by
        exact mul_le_mul_of_nonneg_left hclassA_card (by positivity)
      _ = (C : Real) ^ 2 * Nb * (F'.card : Real) := by ring
  have hNbpos : 0 < Nb := by
    obtain ⟨i, hi⟩ := hs
    let k : iota := U.cover.assign b i
    have hk : k ∈ U.cover.indexSet b := by
      exact U.cover.assign_mem b hb i hi
    have hclassPos : 0 <
        ((Tube.coverClass s (U.cover.assign b) k).card : Real) := by
      have : i ∈ Tube.coverClass s (U.cover.assign b) k := by
        simp [Tube.coverClass, k, hi]
      exact_mod_cast (Finset.card_pos.mpr ⟨i, this⟩)
    have hclassUpper :
        ((Tube.coverClass s (U.cover.assign b) k).card : Real) <=
          (C : Real) * Nb := by
      exact_mod_cast U.card_class_le b hb k hk
    nlinarith
  have hchain : Nb * (F.card : Real) <=
      Nb * ((C : Real) ^ 5 * (F'.card : Real)) := by
    calc
      Nb * (F.card : Real) <= (C : Real) ^ 3 * Na := hupper
      _ <= (C : Real) ^ 3 * ((C : Real) ^ 2 * Nb * (F'.card : Real)) := by
        exact mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = Nb * ((C : Real) ^ 5 * (F'.card : Real)) := by ring
  have hbandR : (F.card : Real) <=
      (C : Real) ^ 5 * (F'.card : Real) := by
    exact le_of_mul_le_mul_left hchain hNbpos
  exact_mod_cast hbandR

end
end Kakeya.ml1Boot.W50ExactCountedMiddle

end
