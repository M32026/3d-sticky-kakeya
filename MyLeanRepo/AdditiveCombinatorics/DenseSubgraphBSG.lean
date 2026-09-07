module

/-
# Dense Subgraph Balog-Szemerédi-Gowers Theorem

This module proves a variant of the Balog-Szemerédi-Gowers theorem that
additionally guarantees a dense induced subgraph between the output sets A', B'.

## Key insight

The sets A', B' constructed by the key lemma have the dense subgraph property
by construction: A' is defined as
{a ∈ A : |neighLeft Gph' a ∩ B'| ≥ |B|/(16K²)}.
Thus every a ∈ A' has at least |B|/(16K²) neighbors in B' within Gph'.
Since Gph' ⊆ Gph and B' ⊆ B:

  |Gph ∩ (A' × B')| ≥ |A'| · |B|/(16K²) ≥ |A'| · |B'|/(16K²).

## Main result

`balog_szemeredi_gowers_dense`: same hypotheses as `balog_szemeredi_gowers`,
with the additional conclusion that the induced subgraph has density
at least 1/(16K²).
-/

public import MyLeanRepo.AdditiveCombinatorics.BSG
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 500000

open scoped Pointwise Combinatorics.Additive

namespace AdditiveCombinatorics.BSG

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/--
Strengthened key lemma: same as `bsg_key_lemma`, but additionally exposes
the degree bound that every a ∈ A' has at least |B|/(16K²) neighbors in B'
within the graph Gph'. This is true by the definition of A' in the proof.
-/
theorem bsg_key_lemma_dense
    {A B : Finset G} {Gph' : Finset (G × G)} {K : ℕ}
    (hG : Gph' ⊆ A ×ˢ B) (hK : 1 ≤ K)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h_edges : (Gph'.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)))
    (h_minDeg : ∀ p ∈ Gph', (A.card : ℝ) ≤ (neighRight Gph' p.2).card * (2 * (K : ℝ))) :
    ∃ (A' : Finset G) (B' : Finset G),
      A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℝ) ≥ (A.card : ℝ) / (16 * (K : ℝ)^2) ∧
      (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) ∧
      (∀ a ∈ A', ∀ b ∈ B',
        (path3 Gph' a b : ℝ) ≥
          (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5)) ∧
      (∀ a ∈ A', ((neighLeft Gph' a ∩ B').card : ℝ) ≥
        (B.card : ℝ) / (16 * (K : ℝ)^2)) := by
  classical
  let N (v : G) : Finset G := neighLeft Gph' v
  let badPair := isBadPair Gph' A K
  letI : DecidableRel badPair := Classical.decRel badPair
  let badPairsIn (s : Finset G) : Finset (G × G) :=
    (s ×ˢ s).filter (fun p : G × G => badPair p.1 p.2)
  let Y (v : G) : ℕ := (badPairsIn (N v)).card
  let badPartners (v u : G) : Finset G :=
    (N v).filter (fun w => badPair u w)
  let S (v : G) : Finset G :=
    (N v).filter (fun u => ((badPartners v u).card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2))
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by
    have h : 0 < B.card := Finset.Nonempty.card_pos hB
    exact_mod_cast h
  let badPairsF : Finset (G × G) := (B ×ˢ B).filter (fun (q : G × G) => badPair q.1 q.2)
  have h_main : ∑ v ∈ A, (Y v : ℝ) =
      ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ) := by
    exact sum_badPairs_swap (Gph' := Gph') (A := A) (B := B) (badPair := badPair) hG
  have h1 : ∀ p ∈ badPairsF,
      (commonNeighRight Gph' p.1 p.2 : ℝ) < (A.card : ℝ) / (128 * (K : ℝ)^3) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_sumY : ∑ v ∈ A, (Y v : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3) := by
    rw [h_main]
    have h5 : ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ) ≤
        (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
      calc
        ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ)
          ≤ ∑ _p ∈ badPairsF, (A.card : ℝ) / (128 * (K : ℝ)^3) :=
            Finset.sum_le_sum (fun p hp => (h1 p hp).le)
        _ = (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
          simp [Finset.sum_const] <;> ring
    have h6 : (badPairsF.card : ℝ) ≤ ((B ×ˢ B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h7 : ((B ×ˢ B).card : ℝ) = (B.card : ℝ)^2 := by
      simp [Finset.card_product] <;> ring
    calc
      ∑ p ∈ badPairsF, (commonNeighRight Gph' p.1 p.2 : ℝ)
        ≤ (badPairsF.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h5
      _ ≤ ((B ×ˢ B).card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by gcongr <;> positivity
      _ = (B.card : ℝ)^2 * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by rw [h7] <;> ring
      _ = (A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3) := by ring
  have hS1 : ∀ v ∈ A, ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤ (Y v : ℝ) := by
    intro v _
    have h2 : ∑ u ∈ S v, ((badPartners v u).card : ℝ) ≤ (Y v : ℝ) := by
      have h3 : ∑ u ∈ S v, ((badPartners v u).card : ℝ) ≤
          ∑ u ∈ N v, ((badPartners v u).card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro _ _ _; positivity
      have h4 : ∑ u ∈ N v, (badPartners v u).card = Y v := by
        let S : Finset (G × G) := (N v ×ˢ N v).filter (fun p => badPair p.1 p.2)
        let f : G × G → G := Prod.fst
        have h_maps : (S : Set (G × G)).MapsTo f (N v) := by
          intro p hp
          have h1 : p ∈ N v ×ˢ N v := (Finset.mem_filter.mp hp).1
          exact (Finset.mem_product.mp h1).1
        have h_card : S.card = ∑ u ∈ N v, (S.filter (fun p => p.1 = u)).card :=
          Finset.card_eq_sum_card_fiberwise (H := h_maps)
        have h_fiber : ∀ u ∈ N v, (S.filter (fun p => p.1 = u)).card = (badPartners v u).card := by
          intro u hu
          have h_set_eq : S.filter (fun p => p.1 = u) =
              (badPartners v u).image (fun w : G => (u, w)) := by
            ext p
            constructor
            · intro h
              have h1 : p ∈ S := (Finset.mem_filter.mp h).1
              have h2 : p.1 = u := (Finset.mem_filter.mp h).2
              have h3 : p ∈ N v ×ˢ N v := (Finset.mem_filter.mp h1).1
              have h4 : badPair p.1 p.2 := (Finset.mem_filter.mp h1).2
              have h5 : p.2 ∈ N v := (Finset.mem_product.mp h3).2
              have h6 : badPair u p.2 := by rw [h2] at h4; exact h4
              have h7 : p.2 ∈ badPartners v u := by
                simp only [badPartners, Finset.mem_filter] <;> exact ⟨h5, h6⟩
              have h8 : (u, p.2) = p := by
                apply Prod.ext <;> simp [h2] <;> tauto
              exact Finset.mem_image.mpr ⟨p.2, h7, h8⟩
            · intro h
              rcases Finset.mem_image.mp h with ⟨w, hw, rfl⟩
              have h5 : w ∈ badPartners v u := hw
              have h6 : w ∈ N v := (Finset.mem_filter.mp h5).1
              have h7 : badPair u w := (Finset.mem_filter.mp h5).2
              have h8 : (u, w) ∈ N v ×ˢ N v := Finset.mem_product.mpr ⟨hu, h6⟩
              have h9 : (u, w) ∈ S := Finset.mem_filter.mpr ⟨h8, h7⟩
              exact Finset.mem_filter.mpr ⟨h9, by simp⟩
          rw [h_set_eq]
          have h_inj : Set.InjOn (fun w : G => (u, w)) (badPartners v u : Set G) := by
            intro x _ y _ h
            exact Prod.ext_iff.mp h |>.2
          rw [Finset.card_image_of_injOn h_inj]
        have h_eq1 : S.card = ∑ u ∈ N v, (badPartners v u).card := by
          rw [h_card]
          apply Finset.sum_congr rfl
          intro u hu
          exact h_fiber u hu
        have h_eq2 : S.card = Y v := by rfl
        rw [← h_eq1, h_eq2]
      have h4' : ∑ u ∈ N v, ((badPartners v u).card : ℝ) = (Y v : ℝ) := by
        exact_mod_cast h4
      exact h3.trans_eq h4'
    have h5 : ∀ u ∈ S v, ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤ ((badPartners v u).card : ℝ) := by
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    have h6 : ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2)) ≤
        ∑ u ∈ S v, ((badPartners v u).card : ℝ) := by
      calc
        ((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2))
          = ∑ _u ∈ S v, ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
            simp [Finset.sum_const] <;> ring
        _ ≤ ∑ u ∈ S v, ((badPartners v u).card : ℝ) :=
          Finset.sum_le_sum (fun u hu => h5 u hu)
    exact h6.trans h2
  have hS2 : ∀ v ∈ A, ((S v).card : ℝ) ≤
      (32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ) := by
    intro v hv
    have h4 := hS1 v hv
    have h5 : ((S v).card : ℝ) ≤
        (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
      calc
        ((S v).card : ℝ)
          = (((S v).card : ℝ) * ((B.card : ℝ) / (32 * (K : ℝ)^2))) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by
            field_simp [hBpos.ne'] <;> ring
        _ ≤ (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) := by gcongr
    have h6 : (Y v : ℝ) / ((B.card : ℝ) / (32 * (K : ℝ)^2)) =
        (32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ) := by
      field_simp [hBpos.ne'] <;> ring
    rw [h6] at h5
    exact h5
  have h_sumS : ∑ v ∈ A, ((S v).card : ℝ) ≤
      (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h4 : ∑ v ∈ A, ((S v).card : ℝ) ≤
        ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) :=
      Finset.sum_le_sum (fun v hv => hS2 v hv)
    have h5 : ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) =
        (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := by
      rw [Finset.mul_sum] <;> rfl
    have h6 : ∑ v ∈ A, ((S v).card : ℝ) ≤
        (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := by
      calc
        ∑ v ∈ A, ((S v).card : ℝ)
          ≤ ∑ v ∈ A, ((32 * (K : ℝ)^2) / (B.card : ℝ) * (Y v : ℝ)) := h4
        _ = (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := h5
    have h7 : (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) ≤
        (32 * (K : ℝ)^2) / (B.card : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) := by
      gcongr <;> exact h_sumY
    have h8 : (32 * (K : ℝ)^2) / (B.card : ℝ) *
          ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) =
        (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
      field_simp [hKpos.ne', hBpos.ne'] <;> ring
    calc
      ∑ v ∈ A, ((S v).card : ℝ)
        ≤ (32 * (K : ℝ)^2) / (B.card : ℝ) * ∑ v ∈ A, (Y v : ℝ) := h6
      _ ≤ (32 * (K : ℝ)^2) / (B.card : ℝ) *
            ((A.card : ℝ) * (B.card : ℝ)^2 / (128 * (K : ℝ)^3)) := h7
      _ = (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := h8
  have h_sumN : ∑ v ∈ A, (N v).card = Gph'.card := by
    have h_eq : ∀ v ∈ A, (N v).card = degLeft Gph' v := by
      intro v _
      exact card_neighLeft_eq_degLeft Gph' v
    rw [Finset.sum_congr rfl h_eq]
    exact sum_degLeft_eq_card hG
  have h_sumN' : ∑ v ∈ A, ((N v).card : ℝ) = (Gph'.card : ℝ) := by
    exact_mod_cast h_sumN
  have h_sum_diff : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) ≥
      (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h3 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) =
        (∑ v ∈ A, ((N v).card : ℝ)) - ∑ v ∈ A, ((S v).card : ℝ) := by
      rw [Finset.sum_sub_distrib] <;> rfl
    rw [h3]
    have h4 : (∑ v ∈ A, ((N v).card : ℝ)) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) := by
      rw [h_sumN'] <;> exact h_edges
    have h51 : (∑ v ∈ A, ((S v).card : ℝ)) ≤ (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := h_sumS
    set sumN := (∑ v ∈ A, ((N v).card : ℝ)) with hsumN
    set sumS := (∑ v ∈ A, ((S v).card : ℝ)) with hsumS
    set a1 := (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) with ha1
    set a2 := (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) with ha2
    have h52 : a1 - sumS ≤ sumN - sumS := by
      exact sub_le_sub_right h4 sumS
    have h53 : a1 - a2 ≤ a1 - sumS := by
      exact sub_le_sub_left h51 a1
    have h5 : a1 - a2 ≤ sumN - sumS := le_trans h53 h52
    have h6 : a1 - a2 = a2 := by
      simp only [ha1, ha2]
      field_simp [hKpos.ne'] <;> ring
    have h7 : sumN - sumS ≥ a2 := by
      calc
        sumN - sumS ≥ a1 - a2 := h5
        _ = a2 := h6
    simpa [h3, ha2] using h7
  have h_exists : ∃ v ∈ A, ((N v).card : ℝ) - ((S v).card : ℝ) ≥
      (B.card : ℝ) / (4 * (K : ℝ)) := by
    by_contra h
    push Not at h
    have h5 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) <
        (A.card : ℝ) * ((B.card : ℝ) / (4 * (K : ℝ))) := by
      have h6 : ∑ v ∈ A, (((N v).card : ℝ) - ((S v).card : ℝ)) <
          ∑ _v ∈ A, ((B.card : ℝ) / (4 * (K : ℝ))) := by
        apply Finset.sum_lt_sum_of_nonempty hA
        intro v hv
        exact h v hv
      simpa [Finset.sum_const] using h6
    have h7 : (A.card : ℝ) * ((B.card : ℝ) / (4 * (K : ℝ))) =
        (A.card : ℝ) * (B.card : ℝ) / (4 * (K : ℝ)) := by ring
    rw [h7] at h5
    linarith [h_sum_diff]
  rcases h_exists with ⟨v, hvA, hv_good⟩
  let B' : Finset G := N v \ S v
  have hB'_sub : B' ⊆ B := by
    intro b hb
    have h7 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
    have h8 : (v, b) ∈ Gph' := by simpa [N, neighLeft] using h7
    have h9 : (v, b) ∈ A ×ˢ B := hG h8
    exact (Finset.mem_product.mp h9).2
  have h11 : S v ⊆ N v := Finset.filter_subset _ _
  have hB'_card : (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) := by
    have h_disj : Disjoint (S v) B' := Finset.disjoint_sdiff
    have h_union : S v ∪ B' = N v := by
      simp [B', Finset.union_sdiff_of_subset h11]
    have h_card : (S v).card + B'.card = (N v).card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h10' : (B'.card : ℝ) = ((N v).card : ℝ) - ((S v).card : ℝ) := by
      have h_card' : ((S v).card : ℝ) + (B'.card : ℝ) = ((N v).card : ℝ) := by
        exact_mod_cast h_card
      exact eq_sub_of_add_eq' h_card'
    rw [h10']
    exact hv_good
  let A' : Finset G := A.filter (fun a =>
    ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2))
  have hA'_sub : A' ⊆ A := Finset.filter_subset _ _
  let edgesAB' : Finset (G × G) := Gph'.filter (fun p => p.2 ∈ B')
  have h_maps1 : (edgesAB' : Set (G × G)).MapsTo Prod.fst A := by
    intro p hp
    have h2 : p ∈ Gph' := (Finset.mem_filter.mp hp).1
    have h3 : p ∈ A ×ˢ B := hG h2
    exact (Finset.mem_product.mp h3).1
  have h_fiber1 : ∀ a ∈ A, (edgesAB'.filter (fun p => p.1 = a)).card = (N a ∩ B').card := by
    intro a _
    have h_inj : Set.InjOn Prod.snd ((edgesAB'.filter (fun p => p.1 = a)) : Set (G × G)) := by
      intro p hp q hq h
      have hpf : p.1 = a := (Finset.mem_filter.mp hp).2
      have hqf : q.1 = a := (Finset.mem_filter.mp hq).2
      have h_eq : p.1 = q.1 := by rw [hpf, hqf]
      exact Prod.ext h_eq h
    have h_img : (edgesAB'.filter (fun p => p.1 = a)).image Prod.snd = N a ∩ B' := by
      ext b
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨p, hp_filter, rfl⟩
        have hp_in : p ∈ edgesAB' := (Finset.mem_filter.mp hp_filter).1
        have hp1 : p.1 = a := (Finset.mem_filter.mp hp_filter).2
        have hpG : p ∈ Gph' := (Finset.mem_filter.mp hp_in).1
        have hpB' : p.2 ∈ B' := (Finset.mem_filter.mp hp_in).2
        have h_na : p.2 ∈ N a := by
          have h9 : p = (a, p.2) := by
            apply Prod.ext <;> simp [hp1] <;> tauto
          have h10 : (a, p.2) ∈ Gph' := by rw [← h9]; exact hpG
          simpa [N, neighLeft] using h10
        exact Finset.mem_inter.mpr ⟨h_na, hpB'⟩
      · intro h
        have h_na : b ∈ N a := (Finset.mem_inter.mp h).1
        have h_b' : b ∈ B' := (Finset.mem_inter.mp h).2
        have hG : (a, b) ∈ Gph' := by simpa [N, neighLeft] using h_na
        have h_edge : (a, b) ∈ edgesAB' := Finset.mem_filter.mpr ⟨hG, h_b'⟩
        have h_filter : (a, b) ∈ edgesAB'.filter (fun p => p.1 = a) :=
          Finset.mem_filter.mpr ⟨h_edge, by simp⟩
        exact Finset.mem_image.mpr ⟨(a, b), h_filter, rfl⟩
    rw [← Finset.card_image_of_injOn h_inj, h_img]
  have h_left : (edgesAB'.card : ℝ) = ∑ a ∈ A, ((N a ∩ B').card : ℝ) := by
    have h_card1 : edgesAB'.card = ∑ a ∈ A, (edgesAB'.filter (fun p => p.1 = a)).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps1)
    have h : (edgesAB'.card : ℝ) = ∑ a ∈ A, ((edgesAB'.filter (fun p => p.1 = a)).card : ℝ) := by
      rw [h_card1, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro a ha
    exact_mod_cast h_fiber1 a ha
  have h_maps2 : (edgesAB' : Set (G × G)).MapsTo Prod.snd B' := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_fiber2 : ∀ b ∈ B', (edgesAB'.filter (fun p => p.2 = b)).card = (neighRight Gph' b).card := by
    intro b _
    have h_eq : edgesAB'.filter (fun p => p.2 = b) = Gph'.filter (fun p => p.2 = b) := by
      apply Finset.ext
      intro q
      constructor
      · intro h
        have h1 : q ∈ edgesAB' := (Finset.mem_filter.mp h).1
        have h2 : q.2 = b := (Finset.mem_filter.mp h).2
        have h3 : q ∈ Gph' := (Finset.mem_filter.mp h1).1
        exact Finset.mem_filter.mpr ⟨h3, h2⟩
      · intro h
        have h3 : q ∈ Gph' := (Finset.mem_filter.mp h).1
        have h4 : q.2 = b := (Finset.mem_filter.mp h).2
        have h5 : q.2 ∈ B' := by rw [h4] <;> exact ‹b ∈ B'›
        have h6 : q ∈ edgesAB' := Finset.mem_filter.mpr ⟨h3, h5⟩
        exact Finset.mem_filter.mpr ⟨h6, h4⟩
    rw [h_eq]
    have h_inj : Set.InjOn Prod.fst ((Gph'.filter (fun p => p.2 = b)) : Set (G × G)) := by
      intro p hp q hq h
      have hpf : p.2 = b := (Finset.mem_filter.mp hp).2
      have hqf : q.2 = b := (Finset.mem_filter.mp hq).2
      have h_eq : p.2 = q.2 := by rw [hpf, hqf]
      exact Prod.ext h h_eq
    have h_img : (Gph'.filter (fun p => p.2 = b)).image Prod.fst = neighRight Gph' b := by
      rfl
    rw [← Finset.card_image_of_injOn h_inj, h_img]
  have h_right : (edgesAB'.card : ℝ) = ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) := by
    have h_card2 : edgesAB'.card = ∑ b ∈ B', (edgesAB'.filter (fun p => p.2 = b)).card :=
      Finset.card_eq_sum_card_fiberwise (H := h_maps2)
    have h : (edgesAB'.card : ℝ) = ∑ b ∈ B', ((edgesAB'.filter (fun p => p.2 = b)).card : ℝ) := by
      rw [h_card2, Nat.cast_sum]
    rw [h]
    apply Finset.sum_congr rfl
    intro b hb
    exact_mod_cast h_fiber2 b hb
  have h_eq_both : ∑ a ∈ A, ((N a ∩ B').card : ℝ) = ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) := by
    rw [←h_left, h_right]
  have h_edgesAB : ∑ a ∈ A, ((N a ∩ B').card : ℝ) ≥
      (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) := by
    rw [h_eq_both]
    have h2 : ∀ b ∈ B', (A.card : ℝ) ≤ (neighRight Gph' b).card * (2 * (K : ℝ)) := by
      intro b hb
      have h3 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
      have h4 : (v, b) ∈ Gph' := by simpa [N, neighLeft] using h3
      exact h_minDeg (v, b) h4
    have h3 : ∀ b ∈ B', ((neighRight Gph' b).card : ℝ) ≥ (A.card : ℝ) / (2 * (K : ℝ)) := by
      intro b hb
      have h4 := h2 b hb
      calc
        ((neighRight Gph' b).card : ℝ)
          = (((neighRight Gph' b).card : ℝ) * (2 * (K : ℝ))) / (2 * (K : ℝ)) := by
            field_simp [hKpos.ne'] <;> ring
        _ ≥ (A.card : ℝ) / (2 * (K : ℝ)) := by gcongr
    have h4 : ∑ b ∈ B', ((neighRight Gph' b).card : ℝ) ≥
        (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by
      calc
        ∑ b ∈ B', ((neighRight Gph' b).card : ℝ)
          ≥ ∑ _b ∈ B', (A.card : ℝ) / (2 * (K : ℝ)) := Finset.sum_le_sum (fun b hb => h3 b hb)
        _ = (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) := by simp [Finset.sum_const] <;> ring
    have h7 : (B'.card : ℝ) ≥ (B.card : ℝ) / (4 * (K : ℝ)) := hB'_card
    have h8 : (B'.card : ℝ) * ((A.card : ℝ) / (2 * (K : ℝ))) ≥
        ((B.card : ℝ) / (4 * (K : ℝ))) * ((A.card : ℝ) / (2 * (K : ℝ))) := by gcongr
    have h9 : ((B.card : ℝ) / (4 * (K : ℝ))) * ((A.card : ℝ) / (2 * (K : ℝ))) =
        (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) := by
      field_simp [hKpos.ne'] <;> ring
    linarith [h4, h8, h9]
  have hA'_card : (A'.card : ℝ) ≥ (A.card : ℝ) / (16 * (K : ℝ)^2) := by
    have h_disj : Disjoint A' (A \ A') := Finset.disjoint_sdiff
    have h_union : A' ∪ (A \ A') = A := by
      rw [Finset.union_sdiff_of_subset hA'_sub]
    have h_sum_split : ∑ a ∈ A, ((N a ∩ B').card : ℝ) =
        ∑ a ∈ A', ((N a ∩ B').card : ℝ) + ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) := by
      have h : ∑ a ∈ (A' ∪ (A \ A')), ((N a ∩ B').card : ℝ) =
          ∑ a ∈ A', ((N a ∩ B').card : ℝ) + ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) := by
        rw [Finset.sum_union h_disj] <;> rfl
      rw [h_union] at * <;> exact h
    have h7 : ∑ a ∈ A', ((N a ∩ B').card : ℝ) ≤ (A'.card : ℝ) * (B.card : ℝ) := by
      have h8 : ∀ a ∈ A', ((N a ∩ B').card : ℝ) ≤ (B.card : ℝ) := by
        intro a _
        have h9 : (N a ∩ B').card ≤ B'.card := by
          apply Finset.card_le_card
          exact Finset.inter_subset_right
        have h10 : B'.card ≤ B.card := Finset.card_le_card hB'_sub
        exact_mod_cast le_trans h9 h10
      calc
        ∑ a ∈ A', ((N a ∩ B').card : ℝ)
          ≤ ∑ _a ∈ A', (B.card : ℝ) := Finset.sum_le_sum (fun a ha => h8 a ha)
        _ = (A'.card : ℝ) * (B.card : ℝ) := by simp [Finset.sum_const] <;> ring
    have h10 : ∀ a ∈ A \ A', ((N a ∩ B').card : ℝ) < (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      intro a ha
      have h11 : a ∉ A' := (Finset.mem_sdiff.mp ha).2
      have h12 : a ∈ A := (Finset.mem_sdiff.mp ha).1
      have h13 : ¬(((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2)) := by
        simpa [A', Finset.mem_filter, h12] using h11
      exact not_le.mp h13
    have h11 : ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) ≤
        (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
      have h12 : ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ) ≤
          ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) :=
        Finset.sum_le_sum (fun a ha => (h10 a ha).le)
      have h13 : ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) =
          ((A \ A').card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
        simp [Finset.sum_const] <;> ring
      have h14 : ((A \ A').card : ℝ) ≤ (A.card : ℝ) := by
        have h141 : A \ A' ⊆ A := by simp
        exact_mod_cast Finset.card_le_card h141
      calc
        ∑ a ∈ A \ A', ((N a ∩ B').card : ℝ)
          ≤ ∑ _a ∈ A \ A', (B.card : ℝ) / (16 * (K : ℝ)^2) := h12
        _ = ((A \ A').card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := h13
        _ ≤ (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by gcongr <;> exact h14
    have h5 : ∑ a ∈ A, ((N a ∩ B').card : ℝ) ≤
        (A'.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) := by
      rw [h_sum_split]
      linarith [h7, h11]
    have h10' : (A.card : ℝ) * ((B.card : ℝ) / (16 * (K : ℝ)^2)) =
        (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      field_simp [hKpos.ne'] <;> ring
    rw [h10'] at h5
    have h_goal : (A'.card : ℝ) * (B.card : ℝ) ≥
        (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      have h1 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) ≤
          (A'.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) :=
        le_trans h_edgesAB h5
      set c := (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) with hc
      have h2 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) - c ≤
          (A'.card : ℝ) * (B.card : ℝ) + c - c := sub_le_sub_right h1 c
      have h3 : (A'.card : ℝ) * (B.card : ℝ) + c - c = (A'.card : ℝ) * (B.card : ℝ) := by ring
      have h4 : (A.card : ℝ) * (B.card : ℝ) / (8 * (K : ℝ)^2) - c = c := by
        simp only [hc]
        field_simp [hKpos.ne'] <;> ring
      rw [h3, h4] at h2
      exact h2
    have h10' : ((A.card : ℝ) / (16 * (K : ℝ)^2)) * (B.card : ℝ) ≤ (A'.card : ℝ) * (B.card : ℝ) := by
      have h_eq : (A.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) =
          ((A.card : ℝ) / (16 * (K : ℝ)^2)) * (B.card : ℝ) := by ring
      rw [h_eq] at h_goal
      exact h_goal
    exact le_of_mul_le_mul_right h10' hBpos
  -- Degree bound: follows directly from definition of A'
  have h_deg : ∀ a ∈ A', ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2) := by
    intro a ha
    have h1 : a ∈ A ∧ ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2) := by
      simpa [A', Finset.mem_filter] using ha
    exact h1.2
  -- Path count
  have h_path : ∀ a ∈ A', ∀ b ∈ B',
      (path3 Gph' a b : ℝ) ≥
        (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) := by
    intro a ha b hb
    have h_na : ((N a ∩ B').card : ℝ) ≥ (B.card : ℝ) / (16 * (K : ℝ)^2) := h_deg a ha
    have h_bad_count : ((badPartners v b).card : ℝ) <
        (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      have h1 : b ∉ S v := (Finset.mem_sdiff.mp hb).2
      have h2 : b ∈ N v := (Finset.mem_sdiff.mp hb).1
      have h3 : ¬(((badPartners v b).card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2)) := by
        simpa [S, Finset.mem_filter, h2] using h1
      exact not_le.mp h3
    have h_bad_subset : (N a ∩ B').filter (fun w => badPair b w) ⊆ badPartners v b := by
      intro w hw
      have h4 : w ∈ N a ∩ B' := (Finset.mem_filter.mp hw).1
      have h5 : w ∈ N v := by
        have h6 : w ∈ B' := (Finset.mem_inter.mp h4).2
        exact (Finset.mem_sdiff.mp h6).1
      simp only [badPartners, Finset.mem_filter]
      exact ⟨h5, (Finset.mem_filter.mp hw).2⟩
    let badInNab : Finset G := (N a ∩ B').filter (fun w => badPair b w)
    let goodB : Finset G := (N a ∩ B').filter (fun w => ¬badPair b w)
    have h_disj : Disjoint goodB badInNab := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : ¬badPair b x := (Finset.mem_filter.mp hx1).2
      have h2 : badPair b x := (Finset.mem_filter.mp hx2).2
      exact h1 h2
    have h_union : goodB ∪ badInNab = N a ∩ B' := by
      ext x
      simp only [goodB, badInNab, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : badPair b x
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    have h1 : (N a ∩ B').card = goodB.card + badInNab.card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h2 : (badInNab.card : ℝ) ≤ ((badPartners v b).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_bad_subset
    have h_bad_lt : (badInNab.card : ℝ) < (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      calc
        (badInNab.card : ℝ) ≤ (badPartners v b).card := h2
        _ < (B.card : ℝ) / (32 * (K : ℝ)^2) := h_bad_count
    have h_good_card : (goodB.card : ℝ) ≥ (B.card : ℝ) / (32 * (K : ℝ)^2) := by
      have h3 : (goodB.card : ℝ) = ((N a ∩ B').card : ℝ) - (badInNab.card : ℝ) := by
        have h4 : ((N a ∩ B').card : ℝ) = (goodB.card : ℝ) + (badInNab.card : ℝ) := by
          exact_mod_cast h1
        linarith
      rw [h3]
      have h5 : (B.card : ℝ) / (16 * (K : ℝ)^2) - (B.card : ℝ) / (32 * (K : ℝ)^2) ≤
          ((N a ∩ B').card : ℝ) - (badInNab.card : ℝ) := by
        exact sub_le_sub h_na h_bad_lt.le
      have h6 : (B.card : ℝ) / (16 * (K : ℝ)^2) - (B.card : ℝ) / (32 * (K : ℝ)^2) =
          (B.card : ℝ) / (32 * (K : ℝ)^2) := by
        field_simp [hKpos.ne'] <;> ring
      linarith [h5, h6]
    have h_common : ∀ b' ∈ goodB,
        (commonNeighRight Gph' b b' : ℝ) ≥ (A.card : ℝ) / (128 * (K : ℝ)^3) := by
      intro b' hb'
      have h4 : ¬badPair b b' := (Finset.mem_filter.mp hb').2
      exact not_lt.mp h4
    let pathSet : Finset (G × G) := goodB.biUnion (fun b' =>
      (neighRight Gph' b ∩ neighRight Gph' b').image (fun a' => (b', a')))
    have h_subset : pathSet ⊆ path3Set Gph' a b := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨b', hb', hpin⟩
      rcases Finset.mem_image.mp hpin with ⟨a', ha', rfl⟩
      have h1 : a' ∈ neighRight Gph' b ∩ neighRight Gph' b' := ha'
      have h2 : a' ∈ neighRight Gph' b := (Finset.mem_inter.mp h1).1
      have h3 : a' ∈ neighRight Gph' b' := (Finset.mem_inter.mp h1).2
      have h4 : (a', b) ∈ Gph' := by simpa [neighRight] using h2
      have h5 : (a', b') ∈ Gph' := by simpa [neighRight] using h3
      have h6 : b' ∈ N a := by
        have h7 : b' ∈ N a ∩ B' := (Finset.mem_filter.mp hb').1
        exact (Finset.mem_inter.mp h7).1
      have h8 : (a, b') ∈ Gph' := by simpa [N, neighLeft] using h6
      exact (mem_path3Set_iff Gph' a b b' a').mpr ⟨h8, h5, h4⟩
    have h_disj2 : ∀ (b1 : G), b1 ∈ goodB → ∀ (b2 : G), b2 ∈ goodB → b1 ≠ b2 →
        Disjoint ((neighRight Gph' b ∩ neighRight Gph' b1).image (fun a' : G => (b1, a')))
          ((neighRight Gph' b ∩ neighRight Gph' b2).image (fun a' : G => (b2, a'))) := by
      intro b1 _ b2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, h_eq1⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, h_eq2⟩
      have h9 : p.1 = b1 := (congr_arg Prod.fst h_eq1).symm
      have h10 : p.1 = b2 := (congr_arg Prod.fst h_eq2).symm
      exact hne (h9.symm.trans h10)
    have h_card_path : pathSet.card = ∑ b' ∈ goodB,
        (neighRight Gph' b ∩ neighRight Gph' b').card := by
      rw [Finset.card_biUnion h_disj2]
      apply Finset.sum_congr rfl
      intro b' _
      have h_inj : Set.InjOn (fun a' : G => (b', a'))
          (↑(neighRight Gph' b ∩ neighRight Gph' b') : Set G) := by
        intro x _ y _ h
        exact Prod.ext_iff.mp h |>.2
      exact Finset.card_image_of_injOn h_inj
    have h_lower : (pathSet.card : ℝ) ≥
        (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
      have h_card_path' : (pathSet.card : ℝ) = ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ) := by
        exact_mod_cast h_card_path
      rw [h_card_path']
      have h : ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ) ≥
          ∑ _b' ∈ goodB, (A.card : ℝ) / (128 * (K : ℝ)^3) :=
        Finset.sum_le_sum (fun b' hb' => h_common b' hb')
      calc
        ∑ b' ∈ goodB, ((neighRight Gph' b ∩ neighRight Gph' b').card : ℝ)
          ≥ ∑ _b' ∈ goodB, (A.card : ℝ) / (128 * (K : ℝ)^3) := h
        _ = (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by
          simp [Finset.sum_const] <;> ring
    have h_final : (path3 Gph' a b : ℝ) ≥ (pathSet.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_subset
    calc
      (path3 Gph' a b : ℝ)
        ≥ (pathSet.card : ℝ) := h_final
      _ ≥ (goodB.card : ℝ) * ((A.card : ℝ) / (128 * (K : ℝ)^3)) := h_lower
      _ ≥ ((B.card : ℝ) / (32 * (K : ℝ)^2)) *
            ((A.card : ℝ) / (128 * (K : ℝ)^3)) := by gcongr
      _ = (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) := by
          norm_num <;> ring
  exact ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, h_path, h_deg⟩

/--
Dense-subgraph variant of the Balog-Szemerédi-Gowers theorem.

Given a bipartite graph `Gph ⊂ A × B` with density at least `1/K` and
restricted sumset size at most `K * sqrt(|A||B|)`, there exist large subsets
`A' ⊆ A`, `B' ⊆ B` such that:
- `|A'| ≥ |A|/K^10`, `|B'| ≥ |B|/K^10`
- `|A'+B'| ≤ 2^12 * K^10 * sqrt(|A||B|)`
- The induced subgraph `Gph ∩ (A' × B')` has density at least `1/(16K²)`.
-/
theorem balog_szemeredi_gowers_dense
    (A B : Finset G) (Gph : Finset (G × G))
    (hG : Gph ⊆ A ×ˢ B)
    (K : ℕ) (hK : 1 ≤ K)
    (h_density : (A.card : ℝ) * (B.card : ℝ) ≤ (K : ℝ) * (Gph.card : ℝ))
    (h_sumset : (restrictedSum A B Gph).card ≤
        (K : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ))) :
    ∃ (A' : Finset G) (B' : Finset G),
      A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) ∧
      (B'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) ∧
      (A' + B').card ≤
        (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ∧
      ((Gph ∩ (A' ×ˢ B')).card : ℝ) ≥
        (A'.card : ℝ) * (B'.card : ℝ) / (16 * (K : ℝ)^2) := by
  classical
  by_cases hA_empty : A = ∅
  · refine' ⟨∅, B, by simp [hA_empty], by simp, _⟩
    have hK10 : (K : ℝ)^10 ≥ 1 := by
      have hK1 : (K : ℝ) ≥ 1 := by exact_mod_cast hK
      have h : (K : ℝ)^10 ≥ (1 : ℝ)^10 := by gcongr
      norm_num at h ⊢ <;> exact h
    constructor
    · simp [hA_empty] <;> positivity
    constructor
    · have h : (B.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) := by
        have hpos : 0 ≤ (B.card : ℝ) := by positivity
        have h2 : 1 / (K : ℝ)^10 ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          exact hK10
        nlinarith
      simpa using h
    constructor
    · have h : (0 : ℝ) ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by positivity
      simpa [hA_empty] using h
    · simp [hA_empty] <;> positivity
  · have hA_ne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
    by_cases hB_empty : B = ∅
    · refine' ⟨A, ∅, by simp, by simp [hB_empty], _⟩
      have hK10 : (K : ℝ)^10 ≥ 1 := by
        have hK1 : (K : ℝ) ≥ 1 := by exact_mod_cast hK
        have h : (K : ℝ)^10 ≥ (1 : ℝ)^10 := by gcongr
        norm_num at h ⊢ <;> exact h
      constructor
      · have h : (A.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) := by
          have hpos : 0 ≤ (A.card : ℝ) := by positivity
          have h2 : 1 / (K : ℝ)^10 ≤ 1 := by
            apply (div_le_one (by positivity)).mpr
            exact hK10
          nlinarith
        simpa using h
      constructor
      · simp [hB_empty] <;> positivity
      constructor
      · have h : (0 : ℝ) ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by positivity
        simpa [hB_empty] using h
      · simp [hB_empty] <;> positivity
    · have hB_ne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB_empty
      by_cases hK1 : K = 1
      · subst hK1
        have hGph_eq : Gph = A ×ˢ B := by
          have h1 : (Gph.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) := by simpa using h_density
          have h2 : Gph.card ≤ (A ×ˢ B).card := Finset.card_le_card hG
          have h3 : (A ×ˢ B).card = A.card * B.card := by
            simp [Finset.card_product] <;> ring
          have h4 : (A ×ˢ B).card ≤ Gph.card := by
            have h5 : ((A ×ˢ B).card : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by exact_mod_cast h3
            have h6 : ((A ×ˢ B).card : ℝ) ≤ (Gph.card : ℝ) := by
              rw [h5]; exact h1
            exact_mod_cast h6
          have h7 : Gph.card = (A ×ˢ B).card := Nat.le_antisymm h2 h4
          exact Finset.eq_of_subset_of_card_le hG h7.symm.le
        have h5 : restrictedSum A B Gph = A + B := by
          rw [hGph_eq] <;> rfl
        rw [h5] at h_sumset
        have h6 : ((A + B).card : ℝ) ≤ (2 : ℝ)^12 * (↑(1 : ℕ) : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
          have h7 : ((A + B).card : ℝ) ≤ (1 : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            simpa using h_sumset
          have h8 : (1 : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) ≤
              (2 : ℝ)^12 * (↑(1 : ℕ) : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            have h9 : 0 ≤ Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := Real.sqrt_nonneg _
            have h10 : (↑(1 : ℕ) : ℝ)^10 = 1 := by norm_num
            rw [h10]
            <;> nlinarith
          exact le_trans h7 h8
        have h_dense : ((Gph ∩ (A ×ˢ B)).card : ℝ) ≥
            (A.card : ℝ) * (B.card : ℝ) / (16 * (↑(1 : ℕ) : ℝ)^2) := by
          have h16 : (16 * (↑(1 : ℕ) : ℝ)^2) = (16 : ℝ) := by norm_num
          rw [h16]
          have h_inter : Gph ∩ (A ×ˢ B) = Gph := by
            exact Finset.inter_eq_left.mpr hG
          rw [h_inter, hGph_eq]
          have h : (A ×ˢ B).card = A.card * B.card := by
            simp [Finset.card_product] <;> ring
          rw [h]
          have h_pos : 0 ≤ (A.card : ℝ) * (B.card : ℝ) := by positivity
          have h16' : (16 : ℝ) ≥ 1 := by norm_num
          have h_le : (A.card : ℝ) * (B.card : ℝ) / 16 ≤ (A.card : ℝ) * (B.card : ℝ) :=
            div_le_self h_pos h16'
          have h_cast : (↑(A.card * B.card) : ℝ) = (A.card : ℝ) * (B.card : ℝ) := by
            exact_mod_cast Nat.cast_mul A.card B.card
          rw [h_cast]
          exact h_le
        exact ⟨A, B, by simp, by simp, by simp, by simp, h6, h_dense⟩
      · -- K ≥ 2 case
        have hK2 : K ≥ 2 := by omega
        have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K from by omega)
        set Gph' : Finset (G × G) := prunedGraph A B Gph K with hGph'
        have hG' : Gph' ⊆ A ×ˢ B := Finset.Subset.trans prunedGraph_subset hG
        have h_edges : (Gph'.card : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2 * (K : ℝ)) :=
          prunedGraph_density hG hK h_density hA_ne hB_ne
        have h_minDeg : ∀ p ∈ Gph', (A.card : ℝ) ≤ (neighRight Gph' p.2).card * (2 * (K : ℝ)) := by
          intro p hp
          have hb : p.2 ∈ Gph'.image Prod.snd := Finset.mem_image_of_mem _ hp
          have h_eq : neighRight Gph' p.2 = neighRight Gph p.2 := prunedGraph_neighRight_eq hb
          rw [h_eq]
          exact_mod_cast prunedGraph_minDegree hp
        rcases bsg_key_lemma_dense (hG := hG') (hK := hK) hA_ne hB_ne h_edges h_minDeg
          with ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, h_path, h_deg⟩
        have hA'_weak : (A'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (A.card : ℝ) := by
          have h1 : (16 : ℝ) * (K : ℝ)^2 ≤ (K : ℝ)^10 := by
            have h2 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h3 : (K : ℝ)^8 ≥ 16 := by
              have h4 : (K : ℝ)^8 ≥ 2^8 := by gcongr <;> norm_num
              norm_num at h4 ⊢ <;> linarith
            have h5 : (K : ℝ)^10 = (K : ℝ)^2 * (K : ℝ)^8 := by ring
            rw [h5]; nlinarith
          have h6 : (A.card : ℝ) / (16 * (K : ℝ)^2) ≥ (A.card : ℝ) / (K : ℝ)^10 := by gcongr
          have h7 : 1 / (K : ℝ)^10 * (A.card : ℝ) = (A.card : ℝ) / (K : ℝ)^10 := by ring
          rw [h7]
          exact le_trans h6 hA'_card
        have hB'_weak : (B'.card : ℝ) ≥ 1 / (K : ℝ)^10 * (B.card : ℝ) := by
          have h1 : (4 : ℝ) * (K : ℝ) ≤ (K : ℝ)^10 := by
            have h2 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h3 : (K : ℝ)^9 ≥ 4 := by
              have h4 : (K : ℝ)^9 ≥ 2^9 := by gcongr <;> norm_num
              norm_num at h4 ⊢ <;> linarith
            nlinarith
          have h6 : (B.card : ℝ) / (4 * (K : ℝ)) ≥ (B.card : ℝ) / (K : ℝ)^10 := by gcongr
          have h7 : 1 / (K : ℝ)^10 * (B.card : ℝ) = (B.card : ℝ) / (K : ℝ)^10 := by ring
          rw [h7]
          exact le_trans h6 hB'_card
        -- DENSITY
        let edgesGph' : Finset (G × G) := Gph' ∩ (A' ×ˢ B')
        have h_edge_count : (edgesGph'.card : ℝ) =
            ∑ a ∈ A', ((neighLeft Gph' a ∩ B').card : ℝ) := by
          have h_maps : (edgesGph' : Set (G × G)).MapsTo Prod.fst A' := by
            intro p hp
            have h2 : p ∈ A' ×ˢ B' := (Finset.mem_inter.mp hp).2
            exact (Finset.mem_product.mp h2).1
          have h_fiber : ∀ a ∈ A', (edgesGph'.filter (fun p => p.1 = a)).card =
              (neighLeft Gph' a ∩ B').card := by
            intro a ha
            have h_inj : Set.InjOn Prod.snd ((edgesGph'.filter (fun p => p.1 = a)) : Set (G × G)) := by
              intro p hp q hq h
              have hpf : p.1 = a := (Finset.mem_filter.mp hp).2
              have hqf : q.1 = a := (Finset.mem_filter.mp hq).2
              have h_eq : p.1 = q.1 := by rw [hpf, hqf]
              exact Prod.ext h_eq h
            have h_img : (edgesGph'.filter (fun p => p.1 = a)).image Prod.snd =
                neighLeft Gph' a ∩ B' := by
              ext b
              constructor
              · intro h
                rcases Finset.mem_image.mp h with ⟨p, hp_filter, rfl⟩
                have hp_in : p ∈ edgesGph' := (Finset.mem_filter.mp hp_filter).1
                have hp1 : p.1 = a := (Finset.mem_filter.mp hp_filter).2
                have hpG : p ∈ Gph' := (Finset.mem_inter.mp hp_in).1
                have hpB' : p.2 ∈ B' := (Finset.mem_product.mp (Finset.mem_inter.mp hp_in).2).2
                have h_na : p.2 ∈ neighLeft Gph' a := by
                  have h9 : p = (a, p.2) := by
                    apply Prod.ext <;> simp [hp1] <;> tauto
                  have h10 : (a, p.2) ∈ Gph' := by rw [← h9]; exact hpG
                  simpa [neighLeft] using h10
                exact Finset.mem_inter.mpr ⟨h_na, hpB'⟩
              · intro h
                have h_na : b ∈ neighLeft Gph' a := (Finset.mem_inter.mp h).1
                have h_b' : b ∈ B' := (Finset.mem_inter.mp h).2
                have hG : (a, b) ∈ Gph' := by simpa [neighLeft] using h_na
                have h_edge : (a, b) ∈ edgesGph' :=
                  Finset.mem_inter.mpr ⟨hG, Finset.mem_product.mpr ⟨ha, h_b'⟩⟩
                have h_filter : (a, b) ∈ edgesGph'.filter (fun p => p.1 = a) :=
                  Finset.mem_filter.mpr ⟨h_edge, by simp⟩
                exact Finset.mem_image.mpr ⟨(a, b), h_filter, rfl⟩
            rw [← Finset.card_image_of_injOn h_inj, h_img]
          have h_card : edgesGph'.card = ∑ a ∈ A', (edgesGph'.filter (fun p => p.1 = a)).card :=
            Finset.card_eq_sum_card_fiberwise (H := h_maps)
          rw [h_card, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro a ha
          exact_mod_cast h_fiber a ha
        have h_edges_lower : (edgesGph'.card : ℝ) ≥
            (A'.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
          rw [h_edge_count]
          have h : ∑ a ∈ A', ((neighLeft Gph' a ∩ B').card : ℝ) ≥
              ∑ _a ∈ A', (B.card : ℝ) / (16 * (K : ℝ)^2) :=
            Finset.sum_le_sum (fun a ha => h_deg a ha)
          have h2 : ∑ _a ∈ A', (B.card : ℝ) / (16 * (K : ℝ)^2) =
              (A'.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
            simp [Finset.sum_const] <;> ring
          calc
            ∑ a ∈ A', ((neighLeft Gph' a ∩ B').card : ℝ)
              ≥ ∑ _a ∈ A', (B.card : ℝ) / (16 * (K : ℝ)^2) := h
            _ = (A'.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := h2
        have h_sub : edgesGph' ⊆ Gph ∩ (A' ×ˢ B') := by
          intro p hp
          have h1 : p ∈ Gph' := (Finset.mem_inter.mp hp).1
          have h2 : p ∈ A' ×ˢ B' := (Finset.mem_inter.mp hp).2
          have h3 : p ∈ Gph := prunedGraph_subset h1
          exact Finset.mem_inter.mpr ⟨h3, h2⟩
        have hB'_le : (B'.card : ℝ) ≤ (B.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hB'_sub
        have h_dense2 : ((Gph ∩ (A' ×ˢ B')).card : ℝ) ≥
            (A'.card : ℝ) * (B'.card : ℝ) / (16 * (K : ℝ)^2) := by
          have h4 : (edgesGph'.card : ℝ) ≤ ((Gph ∩ (A' ×ˢ B')).card : ℝ) := by
            exact_mod_cast Finset.card_le_card h_sub
          have h5 : (A'.card : ℝ) * (B'.card : ℝ) / (16 * (K : ℝ)^2) ≤
              (A'.card : ℝ) * (B.card : ℝ) / (16 * (K : ℝ)^2) := by
            gcongr <;> exact hB'_le
          exact le_trans h5 (le_trans h_edges_lower h4)
        -- Sumset bound
        set S : Finset G := restrictedSum A B Gph with hS
        have hS_card : (S.card : ℝ) ≤ (K : ℝ) * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := h_sumset
        by_cases h_small : (A.card : ℝ) * (B.card : ℝ) < (2 : ℝ)^13 * (K : ℝ)^5
        · have h_sumset_bound : ((A' + B').card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
            have h : (A' + B').card ≤ A'.card * B'.card := by
              exact Finset.card_image_le.trans (by simp [Finset.card_product] <;> ring)
            have h2 : A'.card * B'.card ≤ A.card * B.card := by
              have h3 : A'.card ≤ A.card := Finset.card_le_card hA'_sub
              have h4 : B'.card ≤ B.card := Finset.card_le_card hB'_sub
              exact mul_le_mul h3 h4 (by positivity) (by positivity)
            exact_mod_cast (le_trans h h2)
          have h_final : (A.card : ℝ) * (B.card : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            set x : ℝ := (A.card : ℝ) * (B.card : ℝ) with hx
            have hx_nonneg : 0 ≤ x := by positivity
            by_cases hx0 : x = 0
            · rw [hx0] <;> positivity
            · have hx_pos : 0 < x := by rw [hx] at * <;> positivity
              have h1 : x ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by
                have h2 : x < (2 : ℝ)^13 * (K : ℝ)^5 := h_small
                have hK1 : (K : ℝ) ≥ 1 := by
                  have h : 1 ≤ K := by linarith
                  exact_mod_cast h
                have h6 : (K : ℝ)^5 ≤ (K : ℝ)^20 := by
                  gcongr <;> norm_num
                have h3 : (2 : ℝ)^13 * (K : ℝ)^5 ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by
                  gcongr <;> norm_num
                exact le_trans h2.le h3
              have h_sqrt_le : Real.sqrt x ≤ (2 : ℝ)^12 * (K : ℝ)^10 := by
                have h4 : Real.sqrt x ≤ Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) := Real.sqrt_le_sqrt h1
                have h5 : Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) = (2 : ℝ)^12 * (K : ℝ)^10 := by
                  have h6 : 0 ≤ (2 : ℝ)^24 * (K : ℝ)^20 := by positivity
                  have h7 : Real.sqrt ((2 : ℝ)^24 * (K : ℝ)^20) =
                      Real.sqrt ((2 : ℝ)^24) * Real.sqrt ((K : ℝ)^20) := by
                    rw [Real.sqrt_mul (by positivity)]
                  rw [h7]
                  have h8 : Real.sqrt ((2 : ℝ)^24) = (2 : ℝ)^12 := by
                    rw [show (2 : ℝ)^24 = ((2 : ℝ)^12)^2 by ring]
                    rw [Real.sqrt_sq (by positivity)]
                  have h9 : Real.sqrt ((K : ℝ)^20) = (K : ℝ)^10 := by
                    rw [show (K : ℝ)^20 = ((K : ℝ)^10)^2 by ring]
                    rw [Real.sqrt_sq (by positivity)]
                  rw [h8, h9] <;> ring
                rw [h5] at h4
                exact h4
              have h10 : (Real.sqrt x)^2 = x := Real.sq_sqrt hx_nonneg
              have h11 : x ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
                have h12 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
                have h13 : (Real.sqrt x)^2 ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
                  calc
                    (Real.sqrt x)^2
                      = (Real.sqrt x) * (Real.sqrt x) := by ring
                    _ ≤ ((2 : ℝ)^12 * (K : ℝ)^10) * (Real.sqrt x) := by gcongr <;> exact h_sqrt_le
                    _ = (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by ring
                rw [h10] at h13
                exact h13
              simpa [mul_comm] using h11
          exact ⟨A', B', hA'_sub, hB'_sub, hA'_weak, hB'_weak,
            le_trans h_sumset_bound h_final, h_dense2⟩
        · -- Large case
          have h_large : (A.card : ℝ) * (B.card : ℝ) ≥ (2 : ℝ)^13 * (K : ℝ)^5 := by linarith
          set P_real : ℝ := (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5) with hP_real
          have hP2 : P_real ≥ 2 := by
            rw [hP_real]
            have h : (A.card : ℝ) * (B.card : ℝ) ≥ (2 : ℝ)^13 * (K : ℝ)^5 := h_large
            have hK5_pos : (K : ℝ)^5 > 0 := by positivity
            calc
              (A.card : ℝ) * (B.card : ℝ) / (2^12 * (K : ℝ)^5)
                ≥ ((2 : ℝ)^13 * (K : ℝ)^5) / (2^12 * (K : ℝ)^5) := by gcongr
              _ = 2 := by field_simp [hK5_pos.ne'] <;> norm_num
          let p_int : ℤ := ⌊P_real⌋
          have h_pint_nonneg : 0 ≤ p_int := by
            have h1 : P_real ≥ 2 := hP2
            have h2 : (0 : ℝ) ≤ P_real := by linarith
            exact Int.floor_nonneg.mpr h2
          let p : ℕ := Int.toNat p_int
          have h_coe_int : (p : ℤ) = p_int := Int.toNat_of_nonneg h_pint_nonneg
          have hp_coe : (p : ℝ) = (p_int : ℝ) := by exact_mod_cast h_coe_int
          have hp_pos : 0 < p := by
            have h1 : P_real ≥ 2 := hP2
            have h1' : (↑(1 : ℤ) : ℝ) ≤ P_real := by exact_mod_cast (show (1 : ℝ) ≤ P_real from by linarith)
            have h2 : (1 : ℤ) ≤ p_int := Int.le_floor.mpr h1'
            have h3 : (p : ℤ) ≥ 1 := by rw [h_coe_int] <;> exact h2
            exact_mod_cast h3
          have hp_lower : (p : ℝ) ≥ P_real / 2 := by
            have h1 : (p_int : ℝ) ≥ P_real - 1 := Int.sub_one_lt_floor P_real |>.le
            have h2 : P_real - 1 ≥ P_real / 2 := by linarith
            have h3 : (p : ℝ) = (p_int : ℝ) := hp_coe
            rw [h3]; linarith
          have hP_lower : (p : ℝ) ≥ (A.card : ℝ) * (B.card : ℝ) / (2^13 * (K : ℝ)^5) := by
            have h3 : P_real / 2 = (A.card : ℝ) * (B.card : ℝ) / (2^13 * (K : ℝ)^5) := by
              rw [hP_real] <;> ring
            rw [h3] at hp_lower
            exact hp_lower
          have h_paths_nat : ∀ a ∈ A', ∀ b ∈ B', p ≤ path3 Gph' a b := by
            intro a ha b hb
            have h4 : (path3 Gph' a b : ℝ) ≥ P_real := h_path a ha b hb
            have h5 : (p_int : ℝ) ≤ P_real := Int.floor_le P_real
            have h6 : (p : ℝ) ≤ P_real := by rw [hp_coe] <;> exact h5
            have h7 : (p : ℝ) ≤ (path3 Gph' a b : ℝ) := le_trans h6 h4
            exact_mod_cast h7
          set S' : Finset G := restrictedSum A B Gph' with hS'
          have hS'_sub_S : S' ⊆ S := by
            apply Finset.image_subset_image _
            exact prunedGraph_subset
          have hS'_card : S'.card ≤ S.card := Finset.card_le_card hS'_sub_S
          have h_bound : p * (A' + B').card ≤ S'.card ^ 3 :=
            path_to_sumset_bound hA'_sub hB'_sub S' rfl p hp_pos h_paths_nat
          have h6 : (p : ℝ) * ((A' + B').card : ℝ) ≤ (S'.card : ℝ)^3 := by exact_mod_cast h_bound
          have h7 : ((A' + B').card : ℝ) ≤ (S'.card : ℝ)^3 / (p : ℝ) := by
            have hp_pos' : (p : ℝ) > 0 := by exact_mod_cast hp_pos
            calc
              ((A' + B').card : ℝ)
                = ((p : ℝ) * ((A' + B').card : ℝ)) / (p : ℝ) := by
                  field_simp [hp_pos'.ne'] <;> ring
              _ ≤ (S'.card : ℝ)^3 / (p : ℝ) := by gcongr
          set x : ℝ := (A.card : ℝ) * (B.card : ℝ) with hx
          have hx_pos : 0 < x := by positivity
          have h9 : (S'.card : ℝ) ≤ (K : ℝ) * Real.sqrt x := by
            calc
              (S'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hS'_card
              _ ≤ (K : ℝ) * Real.sqrt x := hS_card
          have h10 : (S'.card : ℝ)^3 ≤ (K : ℝ)^3 * x * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3
                ≤ ((K : ℝ) * Real.sqrt x) ^ 3 := by gcongr
              _ = (K : ℝ)^3 * (Real.sqrt x) ^ 3 := by ring
              _ = (K : ℝ)^3 * (x * Real.sqrt x) := by
                have h11 : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
                  have h12 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by positivity)
                  calc
                    (Real.sqrt x) ^ 3 = (Real.sqrt x) ^ 2 * Real.sqrt x := by ring
                    _ = x * Real.sqrt x := by rw [h12] <;> ring
                rw [h11] <;> ring
              _ = (K : ℝ)^3 * x * Real.sqrt x := by ring
          have h13 : (p : ℝ) ≥ x / (2^13 * (K : ℝ)^5) := hP_lower
          have h14 : (S'.card : ℝ)^3 / (p : ℝ) ≤
              (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3 / (p : ℝ)
                ≤ ((K : ℝ)^3 * x * Real.sqrt x) / (x / (2^13 * (K : ℝ)^5)) := by gcongr
              _ = (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := by
                field_simp [hx_pos.ne'] <;> ring
          have h15 : (2 : ℝ)^13 * (K : ℝ)^8 ≤ (2 : ℝ)^12 * (K : ℝ)^10 := by
            have h16 : (K : ℝ) ≥ 2 := by exact_mod_cast hK2
            have h17 : (2 : ℝ) ≤ (K : ℝ)^2 := by
              have h18 : (K : ℝ)^2 ≥ 4 := by nlinarith
              linarith
            have h18 : (2 : ℝ)^13 * (K : ℝ)^8 = (2 : ℝ)^12 * (2 : ℝ) * (K : ℝ)^8 := by ring
            rw [h18]
            have h19 : (2 : ℝ) * (K : ℝ)^8 ≤ (K : ℝ)^2 * (K : ℝ)^8 := by gcongr
            have h20 : (K : ℝ)^2 * (K : ℝ)^8 = (K : ℝ)^10 := by ring
            have h21 : (2 : ℝ)^12 * 2 * (K : ℝ)^8 ≤ (2 : ℝ)^12 * (K : ℝ)^10 := by
              have h22 : (2 : ℝ)^12 * 2 * (K : ℝ)^8 = (2 : ℝ)^12 * ((2 : ℝ) * (K : ℝ)^8) := by ring
              rw [h22]
              have h23 : (2 : ℝ)^12 * ((2 : ℝ) * (K : ℝ)^8) ≤ (2 : ℝ)^12 * ((K : ℝ)^2 * (K : ℝ)^8) := by gcongr
              rw [h20] at h23
              exact h23
            exact h21
          have h8 : (S'.card : ℝ)^3 / (p : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by
            calc
              (S'.card : ℝ)^3 / (p : ℝ)
                ≤ (2 : ℝ)^13 * (K : ℝ)^8 * Real.sqrt x := h14
              _ ≤ (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt x := by gcongr <;> exact h15
          have h_final : ((A' + B').card : ℝ) ≤
              (2 : ℝ)^12 * (K : ℝ)^10 * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
            simpa [hx] using le_trans h7 h8
          exact ⟨A', B', hA'_sub, hB'_sub, hA'_weak, hB'_weak, h_final, h_dense2⟩

end AdditiveCombinatorics.BSG
