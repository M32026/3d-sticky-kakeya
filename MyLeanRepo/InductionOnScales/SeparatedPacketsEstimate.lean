module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Separated packets cardinality estimate

Abstract lemma proving h_est3 (form46) via separated tube packets.
`|TQ_local| ≥ |fineTubes| * m_Q / 8`
-/

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

section SeparatedPacketsEstimate

/-- Two local tubes are "separated" if different slope, or same slope
and intercept indices differ by at least 8. -/
def AreSeparated {k : ℕ} (U1 U2 : DyadicTube k) : Prop :=
  U1.a ≠ U2.a ∨ |U1.b - U2.b| ≥ 8

/-- Helper: for each slope cell, get a separated subset of intercepts. -/
noncomputable def selectSepSubset {k : ℕ} (fineTubes : Finset (DyadicTube k)) (a : ℤ) : Finset ℤ :=
  Classical.choose (exists_c_separated_subset 7
    ((fineTubes.filter (fun U => U.a = a)).image (fun U => U.b)))

/-- Abstract separated packets estimate. -/
lemma separated_packets_estimate
    {n k : ℕ}
    (fineTubes : Finset (DyadicTube k))
    (TQ_local : Finset (DyadicTube n))
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (packet : DyadicTube k → Finset (DyadicTube n))
    (h_packet_subset : ∀ U ∈ fineTubes, packet U ⊆ TQ_local)
    (h_packet_size : ∀ U ∈ fineTubes, (packet U).card ≥ m_Q)
    (h_disjoint : ∀ U1 ∈ fineTubes, ∀ U2 ∈ fineTubes,
      U1 ≠ U2 → AreSeparated U1 U2 → Disjoint (packet U1) (packet U2)) :
    (TQ_local.card : ℝ) ≥ (fineTubes.card : ℝ) * (m_Q : ℝ) / 8 := by
  let slopeCells : Finset ℤ := fineTubes.image (fun U => U.a)
  let interceptsAt (a : ℤ) : Finset ℤ :=
    (fineTubes.filter (fun U => U.a = a)).image (fun U => U.b)
  let S_a (a : ℤ) : Finset ℤ := selectSepSubset fineTubes a
  have hS_a_sub : ∀ a ∈ slopeCells, S_a a ⊆ interceptsAt a := by
    intro a ha
    exact (Classical.choose_spec (exists_c_separated_subset 7 (interceptsAt a))).1
  have hS_a_sep : ∀ a ∈ slopeCells, ∀ b1 ∈ S_a a, ∀ b2 ∈ S_a a,
      b1 ≠ b2 → |b1 - b2| ≥ 8 := by
    intro a ha
    exact (Classical.choose_spec (exists_c_separated_subset 7 (interceptsAt a))).2.1
  have hS_a_card : ∀ a ∈ slopeCells,
      ((interceptsAt a).card : ℝ) ≤ 8 * ((S_a a).card : ℝ) := by
    intro a ha
    have h_spec := (Classical.choose_spec (exists_c_separated_subset 7 (interceptsAt a))).2.2
    have h : ((interceptsAt a).card : ℝ) ≤ ((7 : ℝ) + 1) * ((S_a a).card : ℝ) := h_spec
    have h8 : ((7 : ℝ) + 1) = (8 : ℝ) := by norm_num
    rw [h8] at h
    exact h
  let selected : Finset (DyadicTube k) :=
    Finset.biUnion slopeCells (fun a => (S_a a).image (fun b => (⟨a, b⟩ : DyadicTube k)))
  have h_selected_sub : selected ⊆ fineTubes := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨a, ha, hU'⟩
    rcases Finset.mem_image.mp hU' with ⟨b, hb, rfl⟩
    have h_b_in : b ∈ interceptsAt a := hS_a_sub a ha hb
    rcases Finset.mem_image.mp h_b_in with ⟨V, hV, h_eq⟩
    have h_va : V.a = a := (Finset.mem_filter.mp hV).2
    have h_vb : V.b = b := h_eq
    have h_U_eq : (⟨a, b⟩ : DyadicTube k) = V := by
      cases V <;> simp [h_va, h_vb] <;> aesop
    rw [h_U_eq]
    exact (Finset.mem_filter.mp hV).1
  have h_selected_separated : ∀ U1 ∈ selected, ∀ U2 ∈ selected,
      U1 ≠ U2 → AreSeparated U1 U2 := by
    intro U1 hU1 U2 hU2 hne
    rcases Finset.mem_biUnion.mp hU1 with ⟨a1, ha1, hU1'⟩
    rcases Finset.mem_biUnion.mp hU2 with ⟨a2, ha2, hU2'⟩
    rcases Finset.mem_image.mp hU1' with ⟨b1, hb1, rfl⟩
    rcases Finset.mem_image.mp hU2' with ⟨b2, hb2, rfl⟩
    by_cases h : a1 = a2
    · subst h
      have h_bne : b1 ≠ b2 := by
        intro h_eq; simp [h_eq] at hne
      have h_far : |b1 - b2| ≥ 8 := hS_a_sep a1 ha1 b1 hb1 b2 hb2 h_bne
      exact Or.inr h_far
    · exact Or.inl h
  have h_packets_disjoint : ∀ U1 ∈ selected, ∀ U2 ∈ selected,
      U1 ≠ U2 → Disjoint (packet U1) (packet U2) := by
    intro U1 hU1 U2 hU2 hne
    have h_U1_in : U1 ∈ fineTubes := h_selected_sub hU1
    have h_U2_in : U2 ∈ fineTubes := h_selected_sub hU2
    have h_sep : AreSeparated U1 U2 := h_selected_separated U1 hU1 U2 hU2 hne
    exact h_disjoint U1 h_U1_in U2 h_U2_in hne h_sep
  let packetUnion := Finset.biUnion selected packet
  have h_union_sub : packetUnion ⊆ TQ_local := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨U, hU, hT'⟩
    exact h_packet_subset U (h_selected_sub hU) hT'
  have h_union_card : (packetUnion.card : ℝ) = ∑ U ∈ selected, ((packet U).card : ℝ) := by
    have h : packetUnion.card = ∑ U ∈ selected, (packet U).card :=
      Finset.card_biUnion h_packets_disjoint
    rw [h] <;> simp
  have h_sum_lower : (∑ U ∈ selected, ((packet U).card : ℝ)) ≥
      (selected.card : ℝ) * (m_Q : ℝ) := by
    have h : ∀ U ∈ selected, (packet U).card ≥ m_Q := by
      intro U hU
      exact h_packet_size U (h_selected_sub hU)
    have h2 : ∑ U ∈ selected, ((packet U).card : ℝ) ≥ ∑ U ∈ selected, (m_Q : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast h i ‹_›
    simpa [Finset.sum_const] using h2
  let cellTubes (a : ℤ) : Finset (DyadicTube k) :=
    fineTubes.filter (fun U => U.a = a)
  have h_disj_cells : ∀ a1 ∈ slopeCells, ∀ a2 ∈ slopeCells,
      a1 ≠ a2 → Disjoint (cellTubes a1) (cellTubes a2) := by
    intro a1 _ a2 _ hne
    simp only [cellTubes, Finset.disjoint_left]
    intro U hU1 hU2
    have h1 : U.a = a1 := (Finset.mem_filter.mp hU1).2
    have h2 : U.a = a2 := (Finset.mem_filter.mp hU2).2
    rw [h1] at h2
    exact hne h2
  have h_cover : fineTubes = Finset.biUnion slopeCells cellTubes := by
    ext U
    simp only [Finset.mem_biUnion, cellTubes, Finset.mem_filter]
    constructor
    · intro hU
      exact ⟨U.a, Finset.mem_image.mpr ⟨U, hU, rfl⟩, hU, rfl⟩
    · rintro ⟨a, _, hU, _⟩; exact hU
  have h_cell_card : ∀ a ∈ slopeCells, (cellTubes a).card = (interceptsAt a).card := by
    intro a _
    have h_inj : Set.InjOn (fun (U : DyadicTube k) => U.b) (cellTubes a) := by
      intro U1 hU1 U2 hU2 h
      have h1 : U1.a = a := (Finset.mem_filter.mp hU1).2
      have h2 : U2.a = a := (Finset.mem_filter.mp hU2).2
      cases U1 <;> cases U2 <;> simp_all <;> aesop
    rw [Finset.card_image_of_injOn h_inj] <;> rfl
  have h_img_card : ∀ a ∈ slopeCells,
      ((S_a a).image (fun b : ℤ => (⟨a, b⟩ : DyadicTube k))).card = (S_a a).card := by
    intro a _
    apply Finset.card_image_of_injective
    intro b1 b2 h; simpa using h
  have h_disj_img : ∀ a1 ∈ slopeCells, ∀ a2 ∈ slopeCells,
      a1 ≠ a2 → Disjoint ((S_a a1).image (fun b => (⟨a1, b⟩ : DyadicTube k)))
        ((S_a a2).image (fun b => (⟨a2, b⟩ : DyadicTube k))) := by
    intro a1 _ a2 _ hne
    simp only [Finset.disjoint_left]
    intro U hU1 hU2
    rcases Finset.mem_image.mp hU1 with ⟨b1, _, rfl⟩
    rcases Finset.mem_image.mp hU2 with ⟨b2, _, h_eq⟩
    injection h_eq with h1 h2
    exact hne h1.symm
  have h_selected_card_eq : (selected.card : ℝ) = ∑ a ∈ slopeCells, ((S_a a).card : ℝ) := by
    have h1 : selected.card = ∑ a ∈ slopeCells, ((S_a a).image (fun b => (⟨a, b⟩ : DyadicTube k))).card :=
      Finset.card_biUnion h_disj_img
    have h2 : (selected.card : ℝ) = ∑ a ∈ slopeCells, (((S_a a).image (fun b => (⟨a, b⟩ : DyadicTube k))).card : ℝ) := by
      rw [h1] <;> simp
    rw [h2]
    apply Finset.sum_congr rfl
    intro a ha
    exact_mod_cast h_img_card a ha
  have h_fine_card : (fineTubes.card : ℝ) = ∑ a ∈ slopeCells, ((cellTubes a).card : ℝ) := by
    have h1 : fineTubes.card = ∑ a ∈ slopeCells, (cellTubes a).card := by
      rw [h_cover]
      exact Finset.card_biUnion h_disj_cells
    rw [h1] <;> simp
  have h_selected_card : (fineTubes.card : ℝ) ≤ 8 * (selected.card : ℝ) := by
    calc (fineTubes.card : ℝ)
      = ∑ a ∈ slopeCells, ((cellTubes a).card : ℝ) := h_fine_card
    _ = ∑ a ∈ slopeCells, ((interceptsAt a).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h_eq : ((cellTubes a).card : ℝ) = ((interceptsAt a).card : ℝ) := by
          exact_mod_cast h_cell_card a ha
        exact h_eq
    _ ≤ ∑ a ∈ slopeCells, 8 * ((S_a a).card : ℝ) := by
        exact Finset.sum_le_sum (fun a ha => hS_a_card a ha)
    _ = 8 * ∑ a ∈ slopeCells, ((S_a a).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = 8 * (selected.card : ℝ) := by rw [←h_selected_card_eq]
  have h_main1 : (TQ_local.card : ℝ) ≥ (packetUnion.card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_union_sub
  have h_main : (TQ_local.card : ℝ) ≥ (selected.card : ℝ) * (m_Q : ℝ) := by
    calc (TQ_local.card : ℝ)
      ≥ (packetUnion.card : ℝ) := h_main1
    _ = ∑ U ∈ selected, ((packet U).card : ℝ) := h_union_card
    _ ≥ (selected.card : ℝ) * (m_Q : ℝ) := h_sum_lower
  have h_final : (selected.card : ℝ) * (m_Q : ℝ) ≥
      (fineTubes.card : ℝ) * (m_Q : ℝ) / 8 := by
    have h2 : (selected.card : ℝ) ≥ (fineTubes.card : ℝ) / 8 := by linarith
    have h_pos : 0 ≤ (m_Q : ℝ) := by positivity
    calc (selected.card : ℝ) * (m_Q : ℝ)
      ≥ ((fineTubes.card : ℝ) / 8) * (m_Q : ℝ) := by gcongr
    _ = (fineTubes.card : ℝ) * (m_Q : ℝ) / 8 := by ring
  exact le_trans h_final h_main

end SeparatedPacketsEstimate

end InductionOnScales
