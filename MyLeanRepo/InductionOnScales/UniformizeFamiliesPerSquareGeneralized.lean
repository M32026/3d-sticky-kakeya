module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.PacketUniformization
public import MyLeanRepo.InductionOnScales.FinePhasePigeonhole
public import MyLeanRepo.InductionOnScales.NiceConfigHelpers
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Uniformize Families Per Square

Given retained tube families for points within a single coarse square Q,
uniformize the slope-cell packet sizes and cell counts across all points.

K_loss = 16 * L^2 where L = numDyadicLevels M.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Truncate every packet of a uniformly-sized family to m_Q tubes. -/
lemma truncate_packets_uniform
    {n m : ℕ} {G : Finset (DyadicTube n)} {m_orig m_Q : ℕ}
    (hG_nonempty : G.Nonempty)
    (hmQ_pos : 0 < m_Q) (h_le : m_Q ≤ m_orig) (h_lt : m_orig < 2 * m_Q)
    (h_uniform : ∀ a, a ∈ occupiedCells m G →
      (FinePhase.packetOf' m G a).card = m_orig) :
    ∃ (G' : Finset (DyadicTube n)),
      G' ⊆ G ∧
      (∀ a, (FinePhase.packetOf' m G' a).card =
        if a ∈ occupiedCells m G' then m_Q else 0) ∧
      occupiedCells m G' = occupiedCells m G ∧
      G.card ≤ 2 * G'.card := by
  let cells := occupiedCells m G
  have h_cells_nonempty : cells.Nonempty := Finset.Nonempty.image hG_nonempty _
  have h_choose : ∀ a ∈ cells, ∃ (P_a : Finset (DyadicTube n)),
      P_a ⊆ FinePhase.packetOf' m G a ∧ P_a.card = m_Q := by
    intro a ha
    have h1 : (FinePhase.packetOf' m G a).card = m_orig := h_uniform a ha
    have h2 : m_Q ≤ (FinePhase.packetOf' m G a).card := by rw [h1] <;> exact h_le
    exact Finset.exists_subset_card_eq h2
  classical
  choose P_a hP_a_sub hP_a_card using h_choose
  let P_a_total (a : ℤ) : Finset (DyadicTube n) :=
    if h : a ∈ cells then P_a a h else ∅
  let G' := cells.biUnion P_a_total
  have hG'_sub : G' ⊆ G := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨a, ha, hT2⟩
    have h1 : P_a_total a ⊆ FinePhase.packetOf' m G a := by
      rw [show P_a_total a = P_a a ha from by simp [P_a_total, ha]]
      exact hP_a_sub a ha
    have h2 : T ∈ FinePhase.packetOf' m G a := h1 hT2
    exact (Finset.mem_filter.mp h2).1
  have h_disj : ∀ a ∈ cells, ∀ b ∈ cells, a ≠ b → Disjoint (P_a_total a) (P_a_total b) := by
    intro a ha b hb hne
    have h1 : P_a_total a ⊆ FinePhase.packetOf' m G a := by simp [P_a_total, ha] <;> exact hP_a_sub a ha
    have h2 : P_a_total b ⊆ FinePhase.packetOf' m G b := by simp [P_a_total, hb] <;> exact hP_a_sub b hb
    have h3 : Disjoint (FinePhase.packetOf' m G a) (FinePhase.packetOf' m G b) := by
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT1).2
      have h5 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hT2).2
      rw [h4] at h5; exact hne h5
    exact Disjoint.mono h1 h2 h3
  have h_cells_eq : occupiedCells m G' = cells := by
    apply Finset.ext
    intro a
    simp only [occupiedCells, Finset.mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      rcases Finset.mem_biUnion.mp hT with ⟨a', ha', hT'⟩
      have h4 : localSlopeCellIndex m T.a = a' := by
        have h5 : P_a_total a' ⊆ FinePhase.packetOf' m G a' := by
          simp [P_a_total, ha'] <;> exact hP_a_sub a' ha'
        have h6 : T ∈ FinePhase.packetOf' m G a' := h5 hT'
        exact (Finset.mem_filter.mp h6).2
      rw [h4] <;> exact ha'
    · intro ha
      have hP_nonempty : (P_a_total a).Nonempty := by
        have h_trim : P_a_total a = P_a a ha := by simp [P_a_total, ha]
        rw [h_trim]
        have h_card_pos : 0 < (P_a a ha).card := by
          rw [hP_a_card a ha] <;> exact hmQ_pos
        exact Finset.card_pos.mp h_card_pos
      rcases hP_nonempty with ⟨T, hT⟩
      have h_cell : localSlopeCellIndex m T.a = a := by
        have h5 : P_a_total a ⊆ FinePhase.packetOf' m G a := by
          simp [P_a_total, ha] <;> exact hP_a_sub a ha
        have h6 : T ∈ FinePhase.packetOf' m G a := h5 hT
        exact (Finset.mem_filter.mp h6).2
      exact ⟨T, Finset.mem_biUnion.mpr ⟨a, ha, hT⟩, h_cell⟩
  have h_uniform' : ∀ a, (FinePhase.packetOf' m G' a).card =
      if a ∈ occupiedCells m G' then m_Q else 0 := by
    intro a
    by_cases ha : a ∈ occupiedCells m G'
    · have ha' : a ∈ cells := by rw [h_cells_eq] at ha; exact ha
      have h_packet_eq : FinePhase.packetOf' m G' a = P_a_total a := by
        apply Finset.ext
        intro T
        have h_iff1 : T ∈ FinePhase.packetOf' m G' a ↔
            T ∈ G' ∧ localSlopeCellIndex m T.a = a := by
          simp [FinePhase.packetOf'] <;> rfl
        have h_iff2 : T ∈ P_a_total a ↔
            T ∈ G' ∧ localSlopeCellIndex m T.a = a := by
          constructor
          · intro hT
            exact ⟨Finset.mem_biUnion.mpr ⟨a, ha', hT⟩, by
              have h5 : P_a_total a ⊆ FinePhase.packetOf' m G a := by
                simp [P_a_total, ha'] <;> exact hP_a_sub a ha'
              have h6 : T ∈ FinePhase.packetOf' m G a := h5 hT
              exact (Finset.mem_filter.mp h6).2⟩
          · rintro ⟨hT, hcell⟩
            rcases Finset.mem_biUnion.mp hT with ⟨a', ha', hT'⟩
            have h10 : localSlopeCellIndex m T.a = a' := by
              have h11 : P_a_total a' ⊆ FinePhase.packetOf' m G a' := by
                simp [P_a_total, ha'] <;> exact hP_a_sub a' ha'
              have h12 : T ∈ FinePhase.packetOf' m G a' := h11 hT'
              exact (Finset.mem_filter.mp h12).2
            have h13 : a' = a := Eq.trans h10.symm hcell
            subst h13
            exact hT'
        rw [h_iff1, h_iff2]
      rw [h_packet_eq]
      have h_trim : P_a_total a = P_a a ha' := by simp [P_a_total, ha']
      rw [h_trim, hP_a_card a ha'] <;> simp [ha]
    · have h_empty : FinePhase.packetOf' m G' a = ∅ := by
        have h_forall : ∀ (T : DyadicTube n), T ∉ FinePhase.packetOf' m G' a := by
          intro T hT
          have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT).2
          have h5 : T ∈ G' := (Finset.mem_filter.mp hT).1
          have h6 : a ∈ occupiedCells m G' := Finset.mem_image.mpr ⟨T, h5, h4⟩
          exact ha h6
        have h_sub : (FinePhase.packetOf' m G' a) ⊆ (∅ : Finset (DyadicTube n)) := by
          intro T hT
          exact False.elim (h_forall T hT)
        simpa using h_sub
      rw [h_empty] <;> simp [ha]
  have h_card_sum : G'.card = ∑ a ∈ cells, (P_a_total a).card :=
    Finset.card_biUnion h_disj
  have hG'_card : G'.card = ∑ a ∈ cells, m_Q := by
    rw [h_card_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have h_trim : P_a_total a = P_a a ha := by simp [P_a_total, ha]
    rw [h_trim]; exact hP_a_card a ha
  have hG_card_sum : G.card = ∑ a ∈ cells, (FinePhase.packetOf' m G a).card :=
    (FinePhase.packet_sum_eq_card m G).symm
  have h_upper : ∀ a ∈ cells, (FinePhase.packetOf' m G a).card < 2 * m_Q := by
    intro a ha
    have h1 : (FinePhase.packetOf' m G a).card = m_orig := h_uniform a ha
    rw [h1]; exact h_lt
  have h_sum_lt : ∑ a ∈ cells, (FinePhase.packetOf' m G a).card < 2 * ∑ a ∈ cells, m_Q := by
    have h : ∑ a ∈ cells, (FinePhase.packetOf' m G a).card < ∑ a ∈ cells, (2 * m_Q) :=
      Finset.sum_lt_sum_of_nonempty h_cells_nonempty (fun a ha => h_upper a ha)
    have h2 : ∑ a ∈ cells, (2 * m_Q) = 2 * ∑ a ∈ cells, m_Q := by
      rw [Finset.mul_sum]
    rw [h2] at h; exact h
  have h_main_card : G.card ≤ 2 * G'.card := by
    rw [hG_card_sum, hG'_card]
    linarith
  exact ⟨G', hG'_sub, h_uniform', h_cells_eq, h_main_card⟩

/-- Select S cells from a uniformly-sized family. -/
lemma select_s_cells_uniform
    {n m : ℕ} {G : Finset (DyadicTube n)} {m_Q S : ℕ}
    (hmQ_pos : 0 < m_Q) (hS_pos : 0 < S)
    (h_uniform : ∀ a, (FinePhase.packetOf' m G a).card =
      if a ∈ occupiedCells m G then m_Q else 0)
    (h_band : S ≤ (occupiedCells m G).card ∧ (occupiedCells m G).card < 2 * S) :
    ∃ (H : Finset (DyadicTube n)) (selectedCells : Finset ℤ),
      H ⊆ G ∧
      selectedCells ⊆ occupiedCells m G ∧
      selectedCells.card = S ∧
      occupiedCells m H = selectedCells ∧
      (∀ a, (FinePhase.packetOf' m H a).card =
        if a ∈ occupiedCells m H then m_Q else 0) ∧
      G.card ≤ 2 * H.card := by
  let cells := occupiedCells m G
  have h1 : S ≤ cells.card := h_band.1
  rcases Finset.exists_subset_card_eq h1 with ⟨selectedCells, hCells_sub, hCells_card⟩
  let H : Finset (DyadicTube n) := selectedCells.biUnion (fun a => FinePhase.packetOf' m G a)
  have hH_sub : H ⊆ G := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨a, _, hT2⟩
    exact (Finset.mem_filter.mp hT2).1
  have h_occupied_H : occupiedCells m H = selectedCells := by
    apply Finset.ext
    intro x
    simp only [occupiedCells, Finset.mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      rcases Finset.mem_biUnion.mp hT with ⟨a', ha', hT'⟩
      have h9 : localSlopeCellIndex m T.a = a' := (Finset.mem_filter.mp hT').2
      rw [h9] <;> exact ha'
    · intro hx
      have h_occ : x ∈ cells := hCells_sub hx
      have h_packet_nonempty : (FinePhase.packetOf' m G x).Nonempty := by
        rcases Finset.mem_image.mp h_occ with ⟨T, hT, rfl⟩
        exact ⟨T, Finset.mem_filter.mpr ⟨hT, rfl⟩⟩
      rcases h_packet_nonempty with ⟨T, hT⟩
      have h10 : localSlopeCellIndex m T.a = x := (Finset.mem_filter.mp hT).2
      exact ⟨T, Finset.mem_biUnion.mpr ⟨x, hx, hT⟩, h10⟩
  have h_uniform_H : ∀ a, (FinePhase.packetOf' m H a).card =
      if a ∈ occupiedCells m H then m_Q else 0 := by
    intro a
    by_cases ha : a ∈ selectedCells
    · have h_packet_eq : FinePhase.packetOf' m H a = FinePhase.packetOf' m G a := by
        apply Finset.ext
        intro T
        have h_iff1 : T ∈ FinePhase.packetOf' m H a ↔
            T ∈ H ∧ localSlopeCellIndex m T.a = a := by
          simp [FinePhase.packetOf'] <;> rfl
        have h_iff2 : T ∈ FinePhase.packetOf' m G a ↔
            T ∈ G ∧ localSlopeCellIndex m T.a = a := by
          simp [FinePhase.packetOf'] <;> rfl
        rw [h_iff1, h_iff2]
        constructor
        · rintro ⟨hT, hcell⟩
          rcases Finset.mem_biUnion.mp hT with ⟨a', ha', hT'⟩
          have h10 : localSlopeCellIndex m T.a = a' := (Finset.mem_filter.mp hT').2
          have h13 : a' = a := Eq.trans h10.symm hcell
          subst h13
          exact ⟨(Finset.mem_filter.mp hT').1, hcell⟩
        · rintro ⟨hT, hcell⟩
          have h14 : T ∈ FinePhase.packetOf' m G a := Finset.mem_filter.mpr ⟨hT, hcell⟩
          exact ⟨Finset.mem_biUnion.mpr ⟨a, ha, h14⟩, hcell⟩
      rw [h_packet_eq]
      have h_occ : a ∈ occupiedCells m H := by rw [h_occupied_H] <;> exact ha
      rw [if_pos h_occ]
      have h_occ_G : a ∈ cells := hCells_sub ha
      have h12 := h_uniform a
      rw [if_pos h_occ_G] at h12 <;> exact h12
    · have h_not_in_H : a ∉ occupiedCells m H := by rw [h_occupied_H] <;> exact ha
      have h_empty : FinePhase.packetOf' m H a = ∅ := by
        have h_forall : ∀ (T : DyadicTube n), T ∉ FinePhase.packetOf' m H a := by
          intro T hT
          have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT).2
          have h5 : T ∈ H := (Finset.mem_filter.mp hT).1
          have h6 : a ∈ occupiedCells m H := Finset.mem_image.mpr ⟨T, h5, h4⟩
          exact h_not_in_H h6
        have h_sub : (FinePhase.packetOf' m H a) ⊆ (∅ : Finset (DyadicTube n)) := by
          intro T hT
          exact False.elim (h_forall T hT)
        simpa using h_sub
      rw [h_empty, if_neg h_not_in_H] <;> simp
  have h_disj2 : ∀ a ∈ selectedCells, ∀ b ∈ selectedCells, a ≠ b →
      Disjoint (FinePhase.packetOf' m G a) (FinePhase.packetOf' m G b) := by
    intro a _ b _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h4 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT1).2
    have h5 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hT2).2
    rw [h4] at h5; exact hne h5
  have hH_card_sum : H.card = ∑ a ∈ selectedCells, (FinePhase.packetOf' m G a).card :=
    Finset.card_biUnion h_disj2
  have h_each : ∀ a ∈ selectedCells, (FinePhase.packetOf' m G a).card = m_Q := by
    intro a ha
    have h_occ : a ∈ cells := hCells_sub ha
    have h12 := h_uniform a
    rw [if_pos h_occ] at h12 <;> exact h12
  have h_sum_const : ∑ a ∈ selectedCells, m_Q = selectedCells.card * m_Q := by
    simp [Finset.sum_const] <;> ring
  have hH_card : H.card = S * m_Q := by
    rw [hH_card_sum, Finset.sum_congr rfl h_each, h_sum_const, hCells_card] <;> ring
  have hG_card_sum : G.card = ∑ a ∈ cells, (FinePhase.packetOf' m G a).card :=
    (FinePhase.packet_sum_eq_card m G).symm
  have h_each2 : ∀ a ∈ cells, (FinePhase.packetOf' m G a).card = m_Q := by
    intro a ha
    have h12 := h_uniform a
    rw [if_pos ha] at h12 <;> exact h12
  have hG_card : G.card = cells.card * m_Q := by
    rw [hG_card_sum, Finset.sum_congr rfl h_each2]
    <;> simp [Finset.sum_const] <;> ring
  have h_main : G.card ≤ 2 * H.card := by
    rw [hG_card, hH_card]
    have h9 : cells.card < 2 * S := h_band.2
    have h10 : cells.card * m_Q < 2 * S * m_Q := mul_lt_mul_of_pos_right h9 hmQ_pos
    have h11 : 2 * S * m_Q = 2 * (S * m_Q) := by ring
    rw [h11] at h10
    exact le_of_lt h10
  exact ⟨H, selectedCells, hH_sub, hCells_sub, hCells_card, h_occupied_H, h_uniform_H, h_main⟩

lemma uniformize_families_per_square_generalized
    {n m : ℕ} (hnm : m ≤ n) (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁) (M : ℕ) (hM : 0 < M)
    (Q : DyadicSquare m)
    (P_Q : Finset (DyadicSquare n))
    (hP_Q_nonempty : P_Q.Nonempty)
    (tubeFamily : (p : DyadicSquare n) → p ∈ P_Q → Finset (DyadicTube n))
    (h_sset : ∀ p hp, IsFiniteTubeSSet s C₁ (tubeFamily p hp))
    (h_size : ∀ p hp, (tubeFamily p hp).card ≤ M)
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp → (T.toSet ∩ p.toSet).Nonempty)
    (h_tube_params : ∀ p hp T, T ∈ tubeFamily p hp → T.IsInAllowedParameterStrip) :
    ∃ (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
      (MQ : ℕ) (hMQ_pos : 0 < MQ)
      (P_Q' : Finset (DyadicSquare n))
      (hP_Q'_sub : P_Q' ⊆ P_Q)
      (hP_Q'_nonempty : P_Q'.Nonempty)
      (uniformFamily : (p : DyadicSquare n) → p ∈ P_Q' → Finset (DyadicTube n))
      (K_loss : ℝ) (hK_loss : 1 ≤ K_loss) (hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2),
      (∀ p hp, uniformFamily p hp ⊆ tubeFamily p (hP_Q'_sub hp)) ∧
      (∀ p hp, ((tubeFamily p (hP_Q'_sub hp)).card : ℝ) ≤ K_loss * ((uniformFamily p hp).card : ℝ)) ∧
      (∀ p hp, IsFiniteTubeSSet s (K_loss * C₁) (uniformFamily p hp)) ∧
      (∀ p hp, ∀ a : ℤ, ((uniformFamily p hp).filter (fun T => localSlopeCellIndex m T.a = a)).card =
          if a ∈ (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) then m_Q else 0) ∧
      (∀ p hp, ((uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip) ∧
      ((P_Q.card : ℝ) ≤ K_loss * (P_Q'.card : ℝ)) := by
  let L := numDyadicLevels M
  have hL_pos : 0 < L := by
    simp [L, numDyadicLevels] <;> omega

  -- Step 1: Within-family uniformization (using actual family size N_p)
  have h_step1 : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q),
      ∃ (m_p : ℕ) (_ : 0 < m_p) (G_p : Finset (DyadicTube n)),
        G_p ⊆ tubeFamily p hp ∧
        G_p.Nonempty ∧
        m_p ≤ (tubeFamily p hp).card ∧
        (∀ a, a ∈ occupiedCells m G_p →
          (FinePhase.packetOf' m G_p a).card = m_p) ∧
        G_p.card ≥ (tubeFamily p hp).card / (2 * L) := by
    intro p hp
    let N_p := (tubeFamily p hp).card
    have hNp_pos : 0 < N_p := (h_sset p hp).1.card_pos
    have hNp_le : N_p ≤ M := h_size p hp
    rcases FinePhase.uniformize_single_family_packets N_p hNp_pos (tubeFamily p hp) rfl with
      ⟨m_p, hm_p_pos, G_p, hG_sub, hG_nonempty, hm_p_le, hG_uniform, hG_card⟩
    have hL_Np_le : numDyadicLevels N_p ≤ L := by
      simp [L, numDyadicLevels] <;> gcongr <;> omega
    have h_card' : G_p.card ≥ N_p / (2 * L) := by
      have h1 : G_p.card ≥ N_p / (2 * numDyadicLevels N_p) := hG_card
      have h2 : 2 * numDyadicLevels N_p ≤ 2 * L := by gcongr
      have h_pos1 : 0 < 2 * numDyadicLevels N_p := by
        have h : 0 < numDyadicLevels N_p := by
          simp [numDyadicLevels] <;> omega
        positivity
      have h3 : N_p / (2 * numDyadicLevels N_p) ≥ N_p / (2 * L) := by
        exact Nat.div_le_div_left h2 h_pos1
      exact le_trans h3 h1
    exact ⟨m_p, hm_p_pos, G_p, hG_sub, hG_nonempty, hm_p_le, hG_uniform, h_card'⟩

  classical
  choose m_p hm_p_pos G_p hG_p_sub hG_p_nonempty hm_p_le hG_p_uniform hG_p_card using h_step1

  let m_p' (p : DyadicSquare n) : ℕ :=
    if h : p ∈ P_Q then m_p p h else 1
  let G_p' (p : DyadicSquare n) : Finset (DyadicTube n) :=
    if h : p ∈ P_Q then G_p p h else ∅

  have h_m_p'_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q), m_p' p = m_p p hp := by
    intro p hp; simp [m_p', hp]
  have h_G_p'_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q), G_p' p = G_p p hp := by
    intro p hp; simp [G_p', hp]

  -- Step 2: Pigeonhole on dyadic level
  let level (p : DyadicSquare n) : ℕ := dyadicLevel (m_p' p)
  have h_level_bound : ∀ p ∈ P_Q, level p < L := by
    intro p hp
    have h1 : m_p' p ≤ M := by
      rw [h_m_p'_eq p hp]
      have h2 : m_p p hp ≤ (tubeFamily p hp).card := hm_p_le p hp
      have h3 : (tubeFamily p hp).card ≤ M := h_size p hp
      exact le_trans h2 h3
    have hpos : 0 < m_p' p := by
      rw [h_m_p'_eq p hp]; exact hm_p_pos p hp
    have hlev_eq : level p = dyadicLevel (m_p' p) := by rfl
    have h3 : dyadicLevel (m_p' p) = Nat.log 2 (m_p' p) + 1 := by
      simp [dyadicLevel, hpos.ne']
    rw [hlev_eq, h3]
    have h4 : Nat.log 2 (m_p' p) ≤ Nat.log 2 M := by gcongr
    simp [L, numDyadicLevels] at * <;> omega

  let P_j (j : ℕ) : Finset (DyadicSquare n) := P_Q.filter (fun p => level p = j)

  have h_partition : (Finset.range L).biUnion P_j = P_Q := by
    apply Finset.ext
    intro p
    simp only [P_j, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hp, _⟩; exact hp
    · intro hp
      have h1 : level p < L := h_level_bound p hp
      exact ⟨level p, h1, hp, rfl⟩

  have h_disj : ∀ j ∈ Finset.range L, ∀ k ∈ Finset.range L, j ≠ k → Disjoint (P_j j) (P_j k) := by
    intro j _ k _ hjk
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : level p = j := (Finset.mem_filter.mp hp1).2
    have h2 : level p = k := (Finset.mem_filter.mp hp2).2
    rw [h1] at h2; exact hjk h2

  have h_sum : ∑ j ∈ Finset.range L, (P_j j).card = P_Q.card := by
    rw [←Finset.card_biUnion h_disj, h_partition]

  have h_range_nonempty : (Finset.range L).Nonempty :=
    Finset.nonempty_range_iff.mpr hL_pos.ne'
  rcases Finset.exists_max_image (Finset.range L) (fun j => (P_j j).card) h_range_nonempty with
    ⟨j, hj_in, h_max⟩

  have hP_j_nonempty : (P_j j).Nonempty := by
    by_contra h_empty
    have h_all_empty : ∀ k ∈ Finset.range L, (P_j k).card = 0 := by
      intro k hk
      have h_le : (P_j k).card ≤ (P_j j).card := h_max k hk
      have h_j0 : (P_j j).card = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp h_empty] <;> simp
      rw [h_j0] at h_le; omega
    have h_sum0 : ∑ k ∈ Finset.range L, (P_j k).card = 0 := by
      rw [Finset.sum_congr rfl h_all_empty] <;> simp
    rw [h_sum0] at h_sum
    have h_PQ0 : P_Q.card = 0 := by linarith
    have h_contra : P_Q = ∅ := Finset.card_eq_zero.mp h_PQ0
    exact hP_Q_nonempty.ne_empty h_contra

  have h_card_bound1 : (P_Q.card : ℝ) ≤ (L : ℝ) * ((P_j j).card : ℝ) := by
    have h1 : ∀ k ∈ Finset.range L, ((P_j k).card : ℝ) ≤ ((P_j j).card : ℝ) := by
      intro k hk; exact_mod_cast h_max k hk
    calc (P_Q.card : ℝ)
      = ∑ k ∈ Finset.range L, ((P_j k).card : ℝ) := by exact_mod_cast h_sum.symm
    _ ≤ ∑ k ∈ Finset.range L, ((P_j j).card : ℝ) := Finset.sum_le_sum h1
    _ = (L : ℝ) * ((P_j j).card : ℝ) := by
      simp [Finset.sum_const] <;> ring

  have hj1 : 1 ≤ j := by
    rcases hP_j_nonempty with ⟨p, hp⟩
    let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hp).1
    have hmp_pos : 0 < m_p' p := by
      rw [h_m_p'_eq p hpQ]; exact hm_p_pos p hpQ
    have hlev : level p = j := (Finset.mem_filter.mp hp).2
    have h1 : 1 ≤ dyadicLevel (m_p' p) := by
      have h2 : m_p' p ≠ 0 := by omega
      simp [dyadicLevel, h2] <;> omega
    have h3 : level p = dyadicLevel (m_p' p) := by rfl
    rw [h3] at hlev
    rw [hlev] at h1
    exact h1

  let m_Q : ℕ := 2 ^ (j - 1)
  have hmQ_pos : 0 < m_Q := by positivity

  have h_m_range : ∀ p ∈ P_j j, m_Q ≤ m_p' p ∧ m_p' p < 2 * m_Q := by
    intro p hp
    let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hp).1
    have hmp_pos : 0 < m_p' p := by
      rw [h_m_p'_eq p hpQ]; exact hm_p_pos p hpQ
    have hlev : level p = j := (Finset.mem_filter.mp hp).2
    have hdl : dyadicLevel (m_p' p) = j := by simpa [level] using hlev
    have h4 : 2 ^ (j - 1) ≤ m_p' p ∧ m_p' p < 2 ^ j := FinePhase.dyadicLevel_range hmp_pos hdl hj1
    have h5 : 2 * m_Q = 2 ^ j := by
      simp [m_Q]
      <;> cases j with
      | zero => omega
      | succ j' => simp [pow_succ] <;> ring
    exact ⟨h4.1, by rw [h5]; exact h4.2⟩

  -- Step 3: Truncate packets to m_Q
  have h_truncate_exists : ∀ (p : DyadicSquare n), p ∈ P_j j →
      ∃ (G' : Finset (DyadicTube n)),
        G' ⊆ G_p' p ∧
        (∀ a : ℤ, (FinePhase.packetOf' m G' a).card =
          if a ∈ occupiedCells m G' then m_Q else 0) ∧
        occupiedCells m G' = occupiedCells m (G_p' p) ∧
        (G_p' p).card ≤ 2 * G'.card := by
    intro p hp
    let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hp).1
    have hG_nonempty : (G_p' p).Nonempty := by
      rw [h_G_p'_eq p hpQ] <;> exact hG_p_nonempty p hpQ
    have h_uniform_orig : ∀ a, a ∈ occupiedCells m (G_p' p) →
        (FinePhase.packetOf' m (G_p' p) a).card = m_p' p := by
      intro a ha
      have ha' : a ∈ occupiedCells m (G_p p hpQ) := by
        rw [←show occupiedCells m (G_p' p) = occupiedCells m (G_p p hpQ) from by
          rw [h_G_p'_eq p hpQ]] <;> exact ha
      have h_unif := hG_p_uniform p hpQ a ha'
      have h_eq1 : FinePhase.packetOf' m (G_p' p) a = FinePhase.packetOf' m (G_p p hpQ) a := by
        rw [h_G_p'_eq p hpQ]
      have h_eq2 : m_p' p = m_p p hpQ := h_m_p'_eq p hpQ
      have h : (FinePhase.packetOf' m (G_p p hpQ) a).card = m_p p hpQ := h_unif
      rw [h_eq1, h_eq2] <;> exact h
    have h_le : m_Q ≤ m_p' p := (h_m_range p hp).1
    have h_lt : m_p' p < 2 * m_Q := (h_m_range p hp).2
    exact truncate_packets_uniform hG_nonempty hmQ_pos h_le h_lt h_uniform_orig

  classical
  choose G'_p hG'_sub hG'_uniform hG'_cells hG'_card using h_truncate_exists

  let G'_p' (p : DyadicSquare n) : Finset (DyadicTube n) :=
    if h : p ∈ P_j j then G'_p p h else ∅

  have h_G'_p'_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P_j j), G'_p' p = G'_p p hp := by
    intro p hp; simp [G'_p', hp]

  -- Step 4: Cell count pigeonhole
  let c (p : DyadicSquare n) : ℕ := (occupiedCells m (G'_p' p)).card

  have hc_bound : ∀ p ∈ P_j j, c p ≤ M := by
    intro p hp
    have h1 : c p = (occupiedCells m (G'_p p hp)).card := by
      simp [c, h_G'_p'_eq p hp]
    rw [h1]
    have h2 : (occupiedCells m (G'_p p hp)).card ≤ (G'_p p hp).card := Finset.card_image_le
    have h3 : (G'_p p hp).card ≤ (G_p' p).card := Finset.card_le_card (hG'_sub p hp)
    have h4 : (G_p' p).card ≤ M := by
      let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hp).1
      have h5 : G_p' p ⊆ tubeFamily p hpQ := by
        rw [h_G_p'_eq p hpQ] <;> exact hG_p_sub p hpQ
      have h6 : (G_p' p).card ≤ (tubeFamily p hpQ).card := Finset.card_le_card h5
      have h7 : (tubeFamily p hpQ).card ≤ M := h_size p hpQ
      exact le_trans h6 h7
    exact le_trans (le_trans h2 h3) h4

  have hc_pos : ∀ p ∈ P_j j, 0 < c p := by
    intro p hp
    have h1 : c p = (occupiedCells m (G'_p p hp)).card := by
      simp [c, h_G'_p'_eq p hp]
    rw [h1]
    have hG'_nonempty : (G'_p p hp).Nonempty := by
      have h_card_pos : 0 < (G'_p p hp).card := by
        have h : (G_p' p).card ≤ 2 * (G'_p p hp).card := hG'_card p hp
        let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hp).1
        have h2 : 0 < (G_p' p).card := by
          rw [h_G_p'_eq p hpQ] <;> exact (hG_p_nonempty p hpQ).card_pos
        omega
      exact Finset.card_pos.mp h_card_pos
    exact Finset.Nonempty.image hG'_nonempty _ |>.card_pos

  rcases cell_count_pigeonhole (P_j j) M hM c hc_bound hc_pos with
    ⟨S, P_Q', hP_Q'_sub, h_band, h_card_bound2⟩

  have hP_Q'_nonempty : P_Q'.Nonempty := by
    by_contra h
    have h0 : P_Q' = ∅ := by simpa using h
    rw [h0] at h_card_bound2
    have h_pos : (0 : ℝ) < ((P_j j).card : ℝ) := by
      exact Nat.cast_pos.mpr hP_j_nonempty.card_pos
    have h_contra : ((P_j j).card : ℝ) ≤ 0 := by simpa using h_card_bound2
    exact not_le.mpr h_pos h_contra

  let hP_Q'_to_PQ : P_Q' ⊆ P_Q := fun p hp =>
    (Finset.mem_filter.mp (hP_Q'_sub hp)).1

  let MQ : ℕ := S
  have hMQ_pos : 0 < MQ := by
    rcases hP_Q'_nonempty with ⟨p, hp⟩
    have h_band_p : S ≤ c p ∧ c p < 2 * S := h_band p hp
    by_contra hS0
    have hS0' : S = 0 := by omega
    rw [hS0'] at h_band_p
    have h3 : c p < 0 := h_band_p.2
    exact Nat.not_lt_zero (c p) h3

  -- Step 5: Select S cells
  have h_select_exists : ∀ (p : DyadicSquare n), p ∈ P_Q' →
      ∃ (H : Finset (DyadicTube n)) (selectedCells : Finset ℤ),
        H ⊆ G'_p' p ∧
        selectedCells ⊆ occupiedCells m (G'_p' p) ∧
        selectedCells.card = S ∧
        occupiedCells m H = selectedCells ∧
        (∀ a, (FinePhase.packetOf' m H a).card =
          if a ∈ occupiedCells m H then m_Q else 0) ∧
        (G'_p' p).card ≤ 2 * H.card := by
    intro p hp
    have hpj : p ∈ P_j j := hP_Q'_sub hp
    have h_band_p : S ≤ c p ∧ c p < 2 * S := h_band p hp
    have h_cp : c p = (occupiedCells m (G'_p p hpj)).card := by
      simp [c, h_G'_p'_eq p hpj]
    have h_band' : S ≤ (occupiedCells m (G'_p p hpj)).card ∧
        (occupiedCells m (G'_p p hpj)).card < 2 * S := by
      rw [←h_cp] <;> exact h_band_p
    have h_uniform' : ∀ a, (FinePhase.packetOf' m (G'_p p hpj) a).card =
        if a ∈ occupiedCells m (G'_p p hpj) then m_Q else 0 := hG'_uniform p hpj
    have h_eq : G'_p' p = G'_p p hpj := h_G'_p'_eq p hpj
    rcases select_s_cells_uniform hmQ_pos hMQ_pos h_uniform' h_band' with
      ⟨H, selectedCells, hH_sub, hCells_sub, hCells_card, h_occupied, h_uniform_H, h_card⟩
    refine ⟨H, selectedCells, ?_⟩
    rw [h_eq] at *
    exact ⟨hH_sub, hCells_sub, hCells_card, h_occupied, h_uniform_H, h_card⟩

  classical
  choose H_p selectedCells hH_sub hCells_sub hCells_card h_occupied_H hH_uniform hH_card_lower using h_select_exists

  have hH_sub_final : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      H_p p hp ⊆ tubeFamily p (show p ∈ P_Q from by
        let hpj : p ∈ P_j j := hP_Q'_sub hp
        exact (Finset.mem_filter.mp hpj).1) := by
    intro p hp
    have hpj : p ∈ P_j j := hP_Q'_sub hp
    let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hpj).1
    have h1 : H_p p hp ⊆ G'_p' p := hH_sub p hp
    have h2 : G'_p' p ⊆ G_p' p := by
      rw [h_G'_p'_eq p hpj] <;> exact hG'_sub p hpj
    have h3 : G_p' p ⊆ tubeFamily p hpQ := by
      rw [h_G_p'_eq p hpQ] <;> exact hG_p_sub p hpQ
    exact Finset.Subset.trans (Finset.Subset.trans h1 h2) h3

  have h_uniform_target : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (a : ℤ),
      ((H_p p hp).filter (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (H_p p hp).image (fun T => localSlopeCellIndex m T.a) then m_Q else 0 := by
    intro p hp a
    have h1 : (H_p p hp).filter (fun T => localSlopeCellIndex m T.a = a) = FinePhase.packetOf' m (H_p p hp) a := by rfl
    rw [h1]
    exact hH_uniform p hp a

  have h_cells_target : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      ((H_p p hp).image (fun T => localSlopeCellIndex m T.a)).card = MQ := by
    intro p hp
    have h1 : (H_p p hp).image (fun T => localSlopeCellIndex m T.a) = occupiedCells m (H_p p hp) := by rfl
    rw [h1, h_occupied_H p hp, hCells_card p hp] <;> rfl

  let K_loss : ℝ := 16 * (L : ℝ)^2
  have hK_loss : 1 ≤ K_loss := by
    have h1 : 1 ≤ (L : ℝ) := by exact_mod_cast hL_pos
    nlinarith

  have h_tube_retention : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      ((tubeFamily p (hP_Q'_to_PQ hp)).card : ℝ) ≤ K_loss * ((H_p p hp).card : ℝ) := by
    intro p hp
    have hpj : p ∈ P_j j := hP_Q'_sub hp
    let hpQ : p ∈ P_Q := (Finset.mem_filter.mp hpj).1
    let N_p := (tubeFamily p hpQ).card
    have hNp_pos : 0 < N_p := (h_sset p hpQ).1.card_pos
    have h2 : (G_p p hpQ).card ≥ N_p / (2 * L) := hG_p_card p hpQ
    have h3 : N_p % (2 * L) < 2 * L := Nat.mod_lt N_p (by positivity)
    have h4 : N_p = (2 * L) * (N_p / (2 * L)) + N_p % (2 * L) := by
      exact Eq.symm (Nat.div_add_mod N_p (2 * L))
    have h_rem_le : N_p % (2 * L) ≤ 2 * L - 1 := by
      have h : N_p % (2 * L) < 2 * L := h3
      exact Nat.le_sub_one_of_lt h
    have h2' : N_p / (2 * L) ≤ (G_p p hpQ).card := h2
    have h_mul : (2 * L) * (N_p / (2 * L)) ≤ (2 * L) * (G_p p hpQ).card :=
      mul_le_mul_of_nonneg_left h2' (by positivity)
    have h1 : N_p ≤ (2 * L) * (G_p p hpQ).card + (2 * L - 1) := by
      have h_eq : N_p = (2 * L) * (N_p / (2 * L)) + N_p % (2 * L) := h4
      rw [h_eq]
      have h_step1 : (2 * L) * (N_p / (2 * L)) + N_p % (2 * L) ≤ (2 * L) * (G_p p hpQ).card + N_p % (2 * L) := by
        have h : (2 * L) * (N_p / (2 * L)) ≤ (2 * L) * (G_p p hpQ).card := h_mul
        linarith
      have h_step2 : (2 * L) * (G_p p hpQ).card + N_p % (2 * L) ≤ (2 * L) * (G_p p hpQ).card + (2 * L - 1) := by
        have h : N_p % (2 * L) ≤ 2 * L - 1 := h_rem_le
        linarith
      linarith
    have hG_pos : 0 < (G_p p hpQ).card := (hG_p_nonempty p hpQ).card_pos
    have hG_ge1 : 1 ≤ (G_p p hpQ).card := hG_pos
    have h_extra : (2 * L - 1 : ℕ) ≤ (2 * L) * (G_p p hpQ).card := by
      have h : (2 * L - 1 : ℕ) ≤ (2 * L) * 1 := by omega
      have h2 : (2 * L) * 1 ≤ (2 * L) * (G_p p hpQ).card := by gcongr <;> omega
      exact le_trans h h2
    have h4' : N_p ≤ 4 * L * (G_p p hpQ).card := by
      calc N_p
        ≤ (2 * L) * (G_p p hpQ).card + (2 * L - 1) := h1
      _ ≤ (2 * L) * (G_p p hpQ).card + (2 * L) * (G_p p hpQ).card := by gcongr
      _ = 4 * L * (G_p p hpQ).card := by ring
    have h5 : (G_p' p).card = (G_p p hpQ).card := by rw [h_G_p'_eq p hpQ]
    have h6 : (G_p' p).card ≤ 2 * (G'_p p hpj).card := hG'_card p hpj
    have h7 : (G'_p' p).card = (G'_p p hpj).card := by rw [h_G'_p'_eq p hpj]
    have h8 : (G'_p' p).card ≤ 2 * (H_p p hp).card := hH_card_lower p hp
    calc (N_p : ℝ)
      ≤ 4 * (L : ℝ) * ((G_p p hpQ).card : ℝ) := by exact_mod_cast h4'
    _ = 4 * (L : ℝ) * ((G_p' p).card : ℝ) := by rw [h5]
    _ ≤ 4 * (L : ℝ) * (2 * ((G'_p p hpj).card : ℝ)) := by gcongr; exact_mod_cast h6
    _ = 8 * (L : ℝ) * ((G'_p' p).card : ℝ) := by rw [h7] <;> ring
    _ ≤ 8 * (L : ℝ) * (2 * ((H_p p hp).card : ℝ)) := by gcongr; exact_mod_cast h8
    _ = 16 * (L : ℝ) * ((H_p p hp).card : ℝ) := by ring
    _ ≤ K_loss * ((H_p p hp).card : ℝ) := by
      have hL_ge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L from by
        simp [L, numDyadicLevels] <;> omega)
      have h_card_nonneg : 0 ≤ ((H_p p hp).card : ℝ) := Nat.cast_nonneg _
      have h_coeff : 16 * (L : ℝ) ≤ K_loss := by
        simp [K_loss] <;> nlinarith
      exact mul_le_mul_of_nonneg_right h_coeff h_card_nonneg

  have h_point_retention : (P_Q.card : ℝ) ≤ K_loss * (P_Q'.card : ℝ) := by
    calc (P_Q.card : ℝ)
      ≤ (L : ℝ) * ((P_j j).card : ℝ) := h_card_bound1
    _ ≤ (L : ℝ) * (((Nat.log 2 M + 2 : ℕ) : ℝ) * (P_Q'.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left h_card_bound2 (by positivity)
    _ = (L : ℝ) * ((L : ℝ) * (P_Q'.card : ℝ)) := by
      have hL_eq : (L : ℝ) = ((Nat.log 2 M + 2 : ℕ) : ℝ) := by
        simp [L, numDyadicLevels] <;> norm_cast
      rw [hL_eq] <;> ring
    _ = (L : ℝ)^2 * (P_Q'.card : ℝ) := by ring
    _ ≤ K_loss * (P_Q'.card : ℝ) := by
      simp [K_loss] <;> nlinarith

  have h_sset_uniform : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q'),
      IsFiniteTubeSSet s (K_loss * C₁) (H_p p hp) := by
    intro p hp
    let hpQ : p ∈ P_Q := by
      let hpj : p ∈ P_j j := hP_Q'_sub hp
      exact (Finset.mem_filter.mp hpj).1
    have h_sub : H_p p hp ⊆ tubeFamily p hpQ := hH_sub_final p hp
    have h_size2 : (tubeFamily p hpQ).card ≤ K_loss * (H_p p hp).card := by
      exact_mod_cast h_tube_retention p hp
    exact subset_tube_family_with_sset h_sub (h_sset p hpQ) h_size2 hK_loss

  have h_incidence_uniform : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (T : DyadicTube n),
      T ∈ H_p p hp → (T.toSet ∩ p.toSet).Nonempty := by
    intro p hp T hT
    let hpQ : p ∈ P_Q := by
      let hpj : p ∈ P_j j := hP_Q'_sub hp
      exact (Finset.mem_filter.mp hpj).1
    have h_sub : T ∈ tubeFamily p hpQ := hH_sub_final p hp hT
    exact h_incidence p hpQ T h_sub

  have h_params_uniform : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q') (T : DyadicTube n),
      T ∈ H_p p hp → T.IsInAllowedParameterStrip := by
    intro p hp T hT
    let hpQ : p ∈ P_Q := by
      let hpj : p ∈ P_j j := hP_Q'_sub hp
      exact (Finset.mem_filter.mp hpj).1
    have h_sub : T ∈ tubeFamily p hpQ := hH_sub_final p hp hT
    exact h_tube_params p hpQ T h_sub

  have hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2 := by
    simp [K_loss, L]
    <;> ring
  exact ⟨m_Q, hmQ_pos, MQ, hMQ_pos, P_Q', hP_Q'_to_PQ, hP_Q'_nonempty, H_p, K_loss, hK_loss, hK_loss_eq,
    hH_sub_final, h_tube_retention, h_sset_uniform, h_uniform_target, h_cells_target,
    h_incidence_uniform, h_params_uniform, h_point_retention⟩

end InductionOnScales
