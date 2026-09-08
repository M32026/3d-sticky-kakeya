/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Tube.IntersectionVolume

/-!
# Reduction to essentially distinct tubes

This file extracts a large pairwise essentially distinct subfamily from a finite tube family,
with the loss controlled by its maximal density.
-/

@[expose] public section

open MeasureTheory
open Topology Convexity

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ι : Type*} [DecidableEq ι]

/-- (blueprint `lem:coverCardBound`) Cardinality of a set covered by few bounded pieces:
if `s ⊆ ⋃ i ∈ s', A i` and every piece has `#(A i) ≤ N`, then `#s ≤ N * #s'`. -/
theorem card_le_card_cover_mul {α β : Type*} [DecidableEq α]
    {s : Finset α} {s' : Finset β} {A : β → Finset α} {N : ℕ}
    (hcover : s ⊆ s'.biUnion A) (hbound : ∀ i ∈ s', (A i).card ≤ N) :
    s.card ≤ N * s'.card := by
  calc
    s.card ≤ (s'.biUnion A).card := Finset.card_le_card hcover
    _ ≤ s'.card * N := Finset.card_biUnion_le_card_mul s' A N hbound
    _ = N * s'.card := Nat.mul_comm _ _

omit [Nontrivial E] [DecidableEq ι] in
/-- (blueprint `lem:existsMaximalEssDistinctSubfamily`) Among subsets of `s` whose tubes are
pairwise essentially distinct there is one that is maximal: every `j ∈ s` not in it fails to be
essentially distinct from some retained tube. -/
theorem Tube.exists_maximal_essDistinct {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) :
    ∃ s' ⊆ s,
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
        ∀ j ∈ s, j ∉ s' →
          ∃ i ∈ s', ¬ IsEssentiallyDistinct (T i).carrier (T j).carrier := by
  classical
  let F : Set (Finset ι) := {s' | s' ⊆ s ∧ (↑s' : Set ι).Pairwise (fun i j =>
    IsEssentiallyDistinct (T i).carrier (T j).carrier)}
  have hF_fin : F.Finite := by
    have : F ⊆ (s.powerset : Set (Finset ι)) := by
      intro s' hs'
      rcases hs' with ⟨hs'sub, _⟩
      exact Finset.mem_powerset.mpr hs'sub
    exact Finset.finite_toSet (s.powerset) |>.subset this
  have hF_nonempty : F.Nonempty := by
    refine ⟨∅, ?_⟩
    refine ⟨Finset.empty_subset s, ?_⟩
    simp
  obtain ⟨s', hs'⟩ := hF_fin.exists_maximal hF_nonempty
  rcases hs' with ⟨⟨hs'sub, hpair⟩, hmax⟩
  refine ⟨s', hs'sub, hpair, ?_⟩
  intro j hj hnot
  by_contra! h
  -- h: ∀ i ∈ s', IsEssentiallyDistinct (T i).carrier (T j).carrier
  have hsub : s' ∪ {j} ⊆ s :=
    Finset.union_subset hs'sub (Finset.singleton_subset_iff.mpr hj)
  have hpair' : (↑(s' ∪ {j}) : Set ι).Pairwise
      (fun i j' => IsEssentiallyDistinct (T i).carrier (T j').carrier) := by
    intro i hi j' hj' hne
    rw [Finset.mem_coe, Finset.mem_union] at hi hj'
    rcases hi with (hi | hi)
    · rcases hj' with (hj' | hj')
      · exact hpair hi hj' hne
      · have hj'_eq : j' = j := Finset.mem_singleton.mp hj'
        subst hj'_eq
        exact h i hi
    · rcases hj' with (hj' | hj')
      · have hi_eq : i = j := Finset.mem_singleton.mp hi
        subst hi_eq
        have hsymm := h j' hj'
        unfold IsEssentiallyDistinct at hsymm ⊢
        rw [Set.inter_comm, max_comm] at hsymm
        exact hsymm
      · have hi_eq : i = j := Finset.mem_singleton.mp hi
        have hj'_eq : j' = j := Finset.mem_singleton.mp hj'
        subst hi_eq
        subst hj'_eq
        exfalso
        exact hne rfl
  have hmem : s' ∪ {j} ∈ F := ⟨hsub, hpair'⟩
  have hss : s' ≤ s' ∪ {j} := Finset.subset_union_left (s₁ := s') (s₂ := {j})
  have hmax' := hmax hmem hss
  have : j ∈ s' := hmax' (by simp)
  exact hnot this

omit [DecidableEq ι] in
/-- (blueprint `lem:tubesInBodyCount`) The number of tubes of the family contained in a convex
body `K`, weighted by the uniform per-tube volume lower bound, is controlled by the maximal
density times `|K|`. -/
theorem card_familyIn_le {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (K : ConvexSpaceBody E) :
    ((familyIn s (fun i => (T i).toConvexSpaceBody) K).card : ENNReal)
        * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
            * (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ maxDensity s (fun i => (T i).toConvexSpaceBody) * volume K.carrier := by
  set n := Module.finrank ℝ E with hn
  set W := fun i : ι => (T i).toConvexSpaceBody
  have hcard_sum : ((familyIn s W K).card : ENNReal)
    * ((Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1)) =
    ∑ i ∈ familyIn s W K, ((Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1)) := by
    rw [Finset.sum_eq_card_nsmul (fun i hi => rfl), nsmul_eq_mul]
  calc
    ((familyIn s W K).card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1))
      = ∑ i ∈ familyIn s W K,
      ((Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1)) := hcard_sum
    _ ≤ ∑ i ∈ familyIn s W K, volume ((T i).carrier) := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact Tube.le_volume (T i)
    _ = ∑ i ∈ familyIn s W K, volume (W i).carrier := by
      simp [W]
    _ = ∑ i ∈ s with W i ≤ K, volume (W i).carrier := rfl
    _ ≤ maxDensity s W * volume K.carrier := sum_volume_le_maxDensity_mul_volume s W K

/-- The large dimensional constant `C_{\ref{lem:refineToEssDistinctLeaves}} = c_n⁻¹` in
`Tube.refineToEssDistinctLeaves`. -/
noncomputable abbrev Tube.refineToEssDistinctLeaves.C (n : ℕ) : ENNReal :=
  Tube.overlapContainment.C n * (Tube.volume_le.C n : ENNReal) / (Tube.le_volume.c n : ENNReal)

omit [DecidableEq ι] in
/-- (blueprint `lem:refineToEssDistinctLeaves`, Reduction to essentially distinct tubes)
Let `T` be a finite family of `δ`-tubes with maximal density at most `D`. Then there is a subfamily
indexed by `s' ⊆ s` whose tubes are pairwise essentially distinct, with
`#s ≤ C_n · D · #s'` (equivalently `#s' ≥ c_n · D⁻¹ · #s` with `c_n = C_n⁻¹`). -/
theorem Tube.refineToEssDistinctLeaves {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E) {D : ENNReal}
    (hD : maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ D) :
    ∃ s' ⊆ s,
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
        (s.card : ENNReal)
          ≤ Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D * (s'.card : ENNReal) := by
  classical
  set n := Module.finrank ℝ E with hn
  set L := (Tube.le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) with hL
  have hLpos : L ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
      (pow_ne_zero _ (by exact_mod_cast hδ0.ne'))
  have hLfin : L ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  -- Volume of a tube is positive and finite
  have hvol_pos (k : ι) : volume ((T k).carrier) ≠ 0 :=
    (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLpos) (Tube.le_volume (T k))).ne'
  have hvol_fin (k : ι) : volume ((T k).carrier) ≠ ⊤ :=
    (T k).isCompact.measure_lt_top.ne
  -- Step 1: maximal essentially distinct subfamily
  obtain ⟨s', hs'sub, hpair, hmax⟩ := Tube.exists_maximal_essDistinct s T
  -- For each i ∈ s' pick a convex body K_i from overlapContainment
  let K (i : ι) : ConvexSpaceBody E :=
    if hi : i ∈ s' then (Tube.overlapContainment hδ0 hδ1 (T i)).choose
    else ConvexSpaceBody.closedUnitBall
  have hKchoose (i) (hi : i ∈ s') :
      K i = (Tube.overlapContainment hδ0 hδ1 (T i)).choose := dif_pos hi
  have hK_vol (i) (hi : i ∈ s') :
      volume (K i).carrier ≤ Tube.overlapContainment.C n * volume (T i).carrier := by
    rw [hKchoose i hi, hn]
    exact (Tube.overlapContainment hδ0 hδ1 (T i)).choose_spec.1
  have hK_cont (i) (hi : i ∈ s') (T' : Tube δ E)
      (h : (1/2 : ENNReal) * volume (T i).carrier < volume ((T i).carrier ∩ T'.carrier)) :
      T'.carrier ⊆ (K i).carrier := by
    rw [hKchoose i hi]
    exact (Tube.overlapContainment hδ0 hδ1 (T i)).choose_spec.2 T' h
  -- A i := family of tubes contained in K_i
  let A (i : ι) : Finset ι := familyIn s (fun k => (T k).toConvexSpaceBody) (K i)
  -- Step 2: cover s ⊆ ⋃_{i ∈ s'} A i
  have hcover : s ⊆ s'.biUnion A := by
    intro j hj
    by_cases hj' : j ∈ s'
    · -- Case 1: j ∈ s', so j ∈ A j by self-overlap
      have hhalf : (1/2 : ENNReal) * volume (T j).carrier < volume ((T j).carrier) := by
        rw [one_div, mul_comm, ← div_eq_mul_inv]
        exact ENNReal.half_lt_self (hvol_pos j) (hvol_fin j)
      have hcap : (T j).carrier ∩ (T j).carrier = (T j).carrier := Set.inter_self _
      have hcont : (T j).carrier ⊆ (K j).carrier :=
        hK_cont j hj' (T j) (by
          simpa [hcap] using hhalf)
      have hmem : j ∈ A j := by
        simp only [A, familyIn, Finset.mem_filter]
        exact ⟨hj, hcont⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj', hmem⟩
    · -- Case 2: j ∉ s', use maximality to get i ∈ s' with non-essentially-distinct
      rcases hmax j hj hj' with ⟨i, hi, hnot⟩
      have hnot_unfold : (1/2 : ENNReal) * max (volume (T i).carrier) (volume (T j).carrier) <
          volume ((T i).carrier ∩ (T j).carrier) :=
        lt_of_not_ge hnot
      have hhalf : (1/2 : ENNReal) * volume (T i).carrier <
          volume ((T i).carrier ∩ (T j).carrier) :=
        calc
          (1/2 : ENNReal) * volume (T i).carrier ≤
              (1/2 : ENNReal) * max (volume (T i).carrier) (volume (T j).carrier) := by
            gcongr; exact le_max_left _ _
          _ < volume ((T i).carrier ∩ (T j).carrier) := hnot_unfold
      have hcont : (T j).carrier ⊆ (K i).carrier := hK_cont i hi (T j) hhalf
      have hmem : j ∈ A i := by
        simp only [A, familyIn, Finset.mem_filter]
        exact ⟨hj, hcont⟩
      exact Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩
  -- Step 3: per-piece bound on card(A i)
  have hcardA (i) (hi : i ∈ s') :
      ((A i).card : ENNReal) ≤ Tube.refineToEssDistinctLeaves.C n * D := by
    -- Treat the (reducible) constant abbreviations as opaque atoms so that `ring` does not
    -- keep unfolding their nested `ENNReal` divisions.
    obtain ⟨oc, hoc⟩ : ∃ x, Tube.overlapContainment.C n = x := ⟨_, rfl⟩
    obtain ⟨Cn, hCn⟩ : ∃ x, Tube.refineToEssDistinctLeaves.C n = x := ⟨_, rfl⟩
    -- The single identity relating the two constants: `Cn * c_n = oc * (volume_le.C n)`.
    have hCc : Cn * (Tube.le_volume.c n : ENNReal) = oc * (Tube.volume_le.C n : ENNReal) := by
      rw [← hCn]
      dsimp only [Tube.refineToEssDistinctLeaves.C]
      rw [hoc]
      exact ENNReal.div_mul_cancel (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
        ENNReal.coe_ne_top
    have hKv : volume (K i).carrier ≤ oc * volume (T i).carrier := by rw [← hoc]; exact hK_vol i hi
    rw [hCn]
    have hineq : ((A i).card : ENNReal) * L ≤ Cn * D * L := by
      calc
        ((A i).card : ENNReal) * L
            ≤ maxDensity s (fun k => (T k).toConvexSpaceBody) * volume (K i).carrier :=
              card_familyIn_le s T (K i)
        _ ≤ D * volume (K i).carrier := by gcongr
        _ ≤ D * (oc * volume (T i).carrier) := by gcongr
        _ ≤ D * (oc * ((Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1))) := by
          gcongr
          exact Tube.volume_le hδ1 (T i)
        _ = Cn * D * L := by
          rw [hL]
          rw [show D * (oc * ((Tube.volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1)))
              = oc * (Tube.volume_le.C n : ENNReal) * D * (δ : ENNReal) ^ (n - 1) from by ring,
            ← hCc]
          ring
    have hcomm : L * ((A i).card : ENNReal) ≤ L * (Cn * D) := by
      rw [mul_comm L ((A i).card : ENNReal), mul_comm L (Cn * D)]; exact hineq
    exact (ENNReal.mul_le_mul_iff_right hLpos hLfin).mp hcomm
  -- Step 4: final inequality
  refine ⟨s', hs'sub, hpair, ?_⟩
  calc
    (s.card : ENNReal) ≤ (∑ i ∈ s', ((A i).card : ENNReal)) := by
      have hcardℕ : s.card ≤ ∑ i ∈ s', (A i).card :=
        (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      exact_mod_cast hcardℕ
    _ ≤ ∑ i ∈ s', (Tube.refineToEssDistinctLeaves.C n * D : ENNReal) :=
      Finset.sum_le_sum fun i hi => hcardA i hi
    _ = (s'.card : ENNReal) * (Tube.refineToEssDistinctLeaves.C n * D : ENNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = Tube.refineToEssDistinctLeaves.C n * D * (s'.card : ENNReal) := mul_comm _ _

end

end Kakeya
