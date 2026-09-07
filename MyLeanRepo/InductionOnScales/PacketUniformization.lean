module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.FinePhasePigeonhole
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Packet Uniformization for Fine Phase

Provides `uniformize_single_family_packets`: trim a tube family to a subset
with uniform packet size m_Q, retaining ≥ 1/(2*log M) fraction of tubes.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales.FinePhase

/-- Packet of tubes in F belonging to slope cell a at scale m. -/
def packetOf' (m : ℕ) {n : ℕ} (F : Finset (DyadicTube n)) (a : ℤ) :
    Finset (DyadicTube n) :=
  F.filter (fun T => localSlopeCellIndex m T.a = a)

/-- Sum of packet sizes equals family size. -/
lemma packet_sum_eq_card (m : ℕ) {n : ℕ} (F : Finset (DyadicTube n)) :
    ∑ a ∈ InductionOnScales.occupiedCells m F, (packetOf' m F a).card = F.card := by
  let S := InductionOnScales.occupiedCells m F
  let packet := packetOf' m F
  have h_disj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (packet a) (packet b) := by
    intro a _ b _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT1).2
    have h5 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hT2).2
    rw [h4] at h5; exact hne h5
  have h1 : S.biUnion packet = F := by
    apply Finset.ext
    intro T
    have h21 : T ∈ S.biUnion packet → T ∈ F := by
      intro h
      rcases Finset.mem_biUnion.mp h with ⟨a, _, hT⟩
      exact (Finset.mem_filter.mp hT).1
    have h22 : T ∈ F → T ∈ S.biUnion packet := by
      intro hT
      let a := localSlopeCellIndex m T.a
      have ha : a ∈ S := Finset.mem_image.mpr ⟨T, hT, rfl⟩
      have hT_in_packet : T ∈ packet a := Finset.mem_filter.mpr ⟨hT, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨a, ha, hT_in_packet⟩
    constructor <;> tauto
  have h_card : (S.biUnion packet).card = ∑ a ∈ S, (packet a).card :=
    Finset.card_biUnion h_disj
  rw [←h_card, h1]

/-- dyadicLevel w = j implies 2^(j-1) ≤ w < 2^j for j ≥ 1 and w > 0. -/
lemma dyadicLevel_range {w j : ℕ} (hwpos : 0 < w) (h : dyadicLevel w = j) (hj1 : 1 ≤ j) :
    2 ^ (j - 1) ≤ w ∧ w < 2 ^ j := by
  have hne : w ≠ 0 := by omega
  have h1 : dyadicLevel w = Nat.log 2 w + 1 := by
    simp [dyadicLevel, hne]
  have h2 : Nat.log 2 w + 1 = j := by
    rw [h1] at h; exact h
  have h3 : 2 ^ (j - 1) ≤ w := by
    have h4 : j - 1 = Nat.log 2 w := by omega
    rw [h4]
    exact Nat.pow_log_le_self 2 hne
  have h4 : w < 2 ^ j := by
    have h5 : j = Nat.log 2 w + 1 := by omega
    rw [h5]
    exact Nat.lt_pow_succ_log_self (by norm_num) w
  exact ⟨h3, h4⟩

/-- Natural division lemma: if S2 ≥ M/L and S2 < 2*S1, then S1 ≥ M/(2*L). -/
lemma div_two_bound (M L S1 S2 : ℕ) (hL_pos : 0 < L)
    (h1 : S2 ≥ M / L) (h2 : S2 < 2 * S1) : S1 ≥ M / (2 * L) := by
  by_cases hS1 : S1 = 0
  · rw [hS1] at h2
    have hS2 : S2 = 0 := by omega
    rw [hS2] at h1
    have hM : M / L = 0 := by omega
    have hM2 : M / (2 * L) = 0 := by
      apply Nat.div_eq_of_lt
      have h : M < 2 * L := by
        by_contra h'
        have h'' : L ≤ M := by omega
        have h3 : M / L > 0 := Nat.div_pos h'' hL_pos
        omega
      omega
    rw [hM2]; omega
  · have hS1_pos : 0 < S1 := by omega
    have h3 : S2 + 1 ≤ 2 * S1 := by omega
    have h4 : M / L + 1 ≤ 2 * S1 := by linarith
    have h5 : S1 ≥ (M / L) / 2 := by omega
    have h6 : (M / L) / 2 = M / (2 * L) := by
      have h7 : (M / L) / 2 = M / (L * 2) := Nat.div_div_eq_div_mul M L 2
      rw [h7]
      have h8 : L * 2 = 2 * L := by ring
      rw [h8]
    rw [h6] at h5
    exact h5

/-- For a single family F, find m_Q and a subset G ⊆ F such that:
- Every occupied cell of G has exactly m_Q tubes
- |G| ≥ |F| / (2 * numDyadicLevels(|F|))
-/
lemma uniformize_single_family_packets
    {n m : ℕ} (M : ℕ) (hM : 0 < M)
    (F : Finset (DyadicTube n)) (hF_card : F.card = M) :
    ∃ (m_Q : ℕ) (hmQ_pos : 0 < m_Q) (G : Finset (DyadicTube n)),
      G ⊆ F ∧
      G.Nonempty ∧
      m_Q ≤ M ∧
      (∀ a, a ∈ InductionOnScales.occupiedCells m G →
        (packetOf' m G a).card = m_Q) ∧
      G.card ≥ M / (2 * numDyadicLevels M) := by
  let cells := InductionOnScales.occupiedCells m F
  let w (a : ℤ) : ℕ := (packetOf' m F a).card
  have h_bound : ∀ a ∈ cells, w a ≤ M := by
    intro a ha
    have h1 : packetOf' m F a ⊆ F := Finset.filter_subset _ _
    have h2 : (packetOf' m F a).card ≤ F.card := Finset.card_le_card h1
    rw [hF_card] at h2; exact h2
  have h_pos : ∀ a ∈ cells, 0 < w a := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨T, hT, rfl⟩
    have hT_in : T ∈ packetOf' m F (localSlopeCellIndex m T.a) :=
      Finset.mem_filter.mpr ⟨hT, rfl⟩
    exact Finset.card_pos.mpr ⟨T, hT_in⟩
  by_cases h_cells_empty : cells = ∅
  · have hF_empty : F = ∅ := by
      by_contra h
      have hF_ne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      have h_cells_ne : cells.Nonempty := Finset.Nonempty.image hF_ne _
      rw [h_cells_empty] at h_cells_ne <;> simpa using h_cells_ne
    simp [hF_empty] at hF_card <;> omega
  · have h_cells_nonempty : cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_cells_empty
    rcases exists_dyadic_level_weighted cells w hM h_bound with
      ⟨j, hj_le, h_weighted⟩
    have h_total_sum : ∑ a ∈ cells, w a = F.card := packet_sum_eq_card m F
    rw [hF_card] at h_total_sum
    by_cases h_triv : M / numDyadicLevels M = 0
    · -- Trivial case: desired bound is ≥ 0, pick any single cell's packet
      have h_goal : M / (2 * numDyadicLevels M) = 0 := by
        apply Nat.div_eq_of_lt
        have h9 : M < numDyadicLevels M := by
          by_contra h10
          have h10' : numDyadicLevels M ≤ M := by omega
          have h11 : 0 < M / numDyadicLevels M := Nat.div_pos h10' (by simp [numDyadicLevels] <;> omega)
          omega
        omega
      rcases h_cells_nonempty with ⟨a, ha⟩
      let G := packetOf' m F a
      let m_Q := w a
      have hmQ_pos : 0 < m_Q := h_pos a ha
      have hG_sub : G ⊆ F := Finset.filter_subset _ _
      have h_uniform : ∀ (x : ℤ), x ∈ InductionOnScales.occupiedCells m G →
          (packetOf' m G x).card = m_Q := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨U, hU, h_eq⟩
        have hU_in : U ∈ G := hU
        have h_cell : localSlopeCellIndex m U.a = a := (Finset.mem_filter.mp hU_in).2
        have hxa : x = a := h_eq.symm.trans h_cell
        rw [hxa]
        have h_packet : packetOf' m G a = G := by
          apply Finset.ext
          intro T
          simp [packetOf', G] <;> tauto
        rw [h_packet]
        <;> rfl
      have h_card : G.card ≥ M / (2 * numDyadicLevels M) := by
        rw [h_goal] <;> exact Nat.zero_le _
      have hG_nonempty : G.Nonempty := by
        have h_pos_card : 0 < G.card := by
          have h : G.card = w a := by rfl
          rw [h]
          exact h_pos a ha
        exact Finset.card_pos.mp h_pos_card
      have hmQ_le : m_Q ≤ M := h_bound a ha
      exact ⟨m_Q, hmQ_pos, G, hG_sub, hG_nonempty, hmQ_le, h_uniform, h_card⟩
    · -- Non-trivial case: M / L > 0
      have h_pos_div : 0 < M / numDyadicLevels M :=
        Nat.pos_of_ne_zero h_triv
      let bandCells := cells.filter (fun a => dyadicLevel (w a) = j)
      have h_band_sum : ∑ a ∈ bandCells, w a ≥ M / numDyadicLevels M := by
        simpa [bandCells, h_total_sum] using h_weighted
      have h_band_nonempty : bandCells.Nonempty := by
        by_contra h
        have h_empty : bandCells = ∅ := by simpa using h
        rw [h_empty] at h_band_sum
        have h_contra : 0 ≥ M / numDyadicLevels M := by simpa using h_band_sum
        exact False.elim (not_le.mpr h_pos_div h_contra)
      have hj1 : 1 ≤ j := by
        by_contra h
        have h0 : j = 0 := by omega
        have h_band_empty : bandCells = ∅ := by
          apply Finset.ext
          intro a
          simp [bandCells, Finset.mem_filter]
          intro ha1 ha2
          rw [h0] at ha2
          have h3 : w a = 0 := by simpa [dyadicLevel] using ha2
          have h4 : 0 < w a := h_pos a ha1
          omega
        rw [h_band_empty] at h_band_nonempty
        simp at h_band_nonempty
      let m_Q := 2 ^ (j - 1)
      have hmQ_pos : 0 < m_Q := by positivity
      have h_band_range : ∀ a ∈ bandCells, m_Q ≤ w a ∧ w a < 2 * m_Q := by
        intro a ha
        have hdl : dyadicLevel (w a) = j := (Finset.mem_filter.mp ha).2
        have hpos : 0 < w a := h_pos a (Finset.mem_filter.mp ha).1
        have h := dyadicLevel_range hpos hdl hj1
        have h4 : w a < 2 * m_Q := by
          have h5 : w a < 2 ^ j := h.2
          have h6 : 2 * m_Q = 2 ^ j := by
            simp [m_Q]
            <;> cases j with
            | zero => omega
            | succ j' => simp [pow_succ] <;> ring
          rw [h6]; exact h5
        exact ⟨h.1, h4⟩
      have h_choose : ∀ a ∈ bandCells,
          ∃ (P_a : Finset (DyadicTube n)), P_a ⊆ packetOf' m F a ∧ P_a.card = m_Q := by
        intro a ha
        have h : m_Q ≤ (packetOf' m F a).card := (h_band_range a ha).1
        exact Finset.exists_subset_card_eq h
      choose P_a hP_a_sub hP_a_card using h_choose
      let P_a_total (a : ℤ) : Finset (DyadicTube n) :=
        if h : a ∈ bandCells then P_a a h else ∅
      let G : Finset (DyadicTube n) := bandCells.biUnion P_a_total
      have hG_sub : G ⊆ F := by
        intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨a, ha, hT2⟩
        have h1 : P_a_total a ⊆ packetOf' m F a := by
          rw [show P_a_total a = P_a a ha from by simp [P_a_total, ha]]
          exact hP_a_sub a ha
        have h2 : T ∈ packetOf' m F a := h1 hT2
        have h3 : T ∈ F := (Finset.mem_filter.mp h2).1
        exact h3
      have h_disj : ∀ a ∈ bandCells, ∀ b ∈ bandCells, a ≠ b →
          Disjoint (P_a_total a) (P_a_total b) := by
        intro a ha b hb hne
        have h1 : P_a_total a ⊆ packetOf' m F a := by
          simp [P_a_total, ha] <;> exact hP_a_sub a ha
        have h2 : P_a_total b ⊆ packetOf' m F b := by
          simp [P_a_total, hb] <;> exact hP_a_sub b hb
        have h3 : Disjoint (packetOf' m F a) (packetOf' m F b) := by
          rw [Finset.disjoint_left]
          intro T hT1 hT2
          have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT1).2
          have h5 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hT2).2
          rw [h4] at h5; exact hne h5
        exact Disjoint.mono h1 h2 h3
      have hG_card : G.card = ∑ a ∈ bandCells, (P_a_total a).card :=
        Finset.card_biUnion h_disj
      have h_uniform : ∀ a, a ∈ InductionOnScales.occupiedCells m G →
          (packetOf' m G a).card = m_Q := by
        intro a ha
        have h_a_in_band : a ∈ bandCells := by
          have hU : ∃ (U : DyadicTube n), U ∈ G ∧ localSlopeCellIndex m U.a = a := by
            have h5 : a ∈ InductionOnScales.occupiedCells m G := ha
            rcases Finset.mem_image.mp h5 with ⟨U, hU, rfl⟩
            exact ⟨U, hU, rfl⟩
          rcases hU with ⟨U, hU_in_G, rfl⟩
          rcases Finset.mem_biUnion.mp hU_in_G with ⟨a', ha', hU'⟩
          have h_sub : P_a_total a' ⊆ packetOf' m F a' := by
            simp [P_a_total, ha'] <;> exact hP_a_sub a' ha'
          have h6 : U ∈ packetOf' m F a' := h_sub hU'
          have h7 : localSlopeCellIndex m U.a = a' := (Finset.mem_filter.mp h6).2
          rw [h7] at *; tauto
        have h_packet_eq : packetOf' m G a = P_a_total a := by
          apply Finset.ext
          intro T
          have h_iff1 : T ∈ packetOf' m G a ↔ T ∈ G ∧ localSlopeCellIndex m T.a = a := by
            simp [packetOf'] <;> rfl
          have h_iff2 : T ∈ P_a_total a ↔ T ∈ G ∧ localSlopeCellIndex m T.a = a := by
            constructor
            · intro hT
              exact ⟨Finset.mem_biUnion.mpr ⟨a, h_a_in_band, hT⟩, by
                have h9 : P_a_total a ⊆ packetOf' m F a := by
                  simp [P_a_total, h_a_in_band] <;> exact hP_a_sub a h_a_in_band
                have h10 : T ∈ packetOf' m F a := h9 hT
                exact (Finset.mem_filter.mp h10).2⟩
            · rintro ⟨hT, hcell⟩
              rcases Finset.mem_biUnion.mp hT with ⟨a', ha', hT'⟩
              have h10 : localSlopeCellIndex m T.a = a' := by
                have h11 : P_a_total a' ⊆ packetOf' m F a' := by
                  simp [P_a_total, ha'] <;> exact hP_a_sub a' ha'
                have h12 : T ∈ packetOf' m F a' := h11 hT'
                exact (Finset.mem_filter.mp h12).2
              rw [h10] at hcell
              rw [hcell] at *
              <;> tauto
          rw [h_iff1, h_iff2]
        rw [h_packet_eq]
        have h_trim : P_a_total a = P_a a h_a_in_band := by simp [P_a_total, h_a_in_band]
        rw [h_trim]; exact hP_a_card a h_a_in_band
      have h_sum_G : G.card = ∑ a ∈ bandCells, m_Q := by
        rw [hG_card]
        apply Finset.sum_congr rfl
        intro a ha
        have h_trim : P_a_total a = P_a a ha := by simp [P_a_total, ha]
        rw [h_trim]; exact hP_a_card a ha
      have h_upper : ∀ a ∈ bandCells, w a < 2 * m_Q := by
        intro a ha; exact (h_band_range a ha).2
      have h_sum_w_lt : ∑ a ∈ bandCells, w a < 2 * ∑ a ∈ bandCells, m_Q := by
        have h : ∑ a ∈ bandCells, w a < ∑ a ∈ bandCells, (2 * m_Q) :=
          Finset.sum_lt_sum_of_nonempty h_band_nonempty (fun a ha => h_upper a ha)
        have h2 : ∑ a ∈ bandCells, (2 * m_Q) = 2 * ∑ a ∈ bandCells, m_Q := by
          rw [Finset.mul_sum]
        rw [h2] at h; exact h
      have h_main_goal : G.card ≥ M / (2 * numDyadicLevels M) := by
        rw [h_sum_G]
        set S1 := ∑ a ∈ bandCells, m_Q with hS1
        set S2 := ∑ a ∈ bandCells, w a with hS2
        exact div_two_bound M (numDyadicLevels M) S1 S2 (by simp [numDyadicLevels] <;> omega) h_band_sum h_sum_w_lt
      have hG_nonempty : G.Nonempty := by
        rcases h_band_nonempty with ⟨a, ha⟩
        have hP_nonempty : (P_a_total a).Nonempty := by
          have h_trim : P_a_total a = P_a a ha := by simp [P_a_total, ha]
          rw [h_trim]
          have h_card_pos : 0 < (P_a a ha).card := by
            rw [hP_a_card a ha] <;> exact hmQ_pos
          exact Finset.card_pos.mp h_card_pos
        rcases hP_nonempty with ⟨T, hT⟩
        exact ⟨T, Finset.mem_biUnion.mpr ⟨a, ha, hT⟩⟩
      have hmQ_le : m_Q ≤ M := by
        rcases h_band_nonempty with ⟨a, ha⟩
        have h1 : m_Q ≤ w a := (h_band_range a ha).1
        have h2 : w a ≤ M := h_bound a (Finset.mem_filter.mp ha).1
        exact le_trans h1 h2
      exact ⟨m_Q, hmQ_pos, G, hG_sub, hG_nonempty, hmQ_le, h_uniform, h_main_goal⟩

end FinePhase

end InductionOnScales
