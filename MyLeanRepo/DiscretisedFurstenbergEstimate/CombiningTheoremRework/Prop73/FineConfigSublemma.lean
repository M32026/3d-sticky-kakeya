module

/-
  Fine config sublemma for Prop73 inductive step.

  Constructs a `CombiningConfig` for the fine tail (n_fine scales) from the
  coarse `CombiningConfig` (n_fine + 1 scales) via B1 bridge decomposition.

  Whiteprint node: combining_theorem_genuine / inductive_step_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DiscretisedFurstenbergEstimate.DyadicConversion

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.RegularIncidence
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.BasicUniformization
open DirecretisedFurstenbergEstimate.FormatConversion.M5

/-- From dyadicDelta k ≤ dyadicDelta m, deduce m ≤ k. -/
lemma dyadicDelta_le_iff {m k : ℕ} :
    dyadicDelta k ≤ dyadicDelta m ↔ m ≤ k := by
  constructor
  · intro h
    by_contra h'
    have h'' : k < m := by omega
    have h3 : (2 : ℝ)^k < (2 : ℝ)^m := by gcongr <;> norm_num
    have h41 : 0 < (2 : ℝ)^k := by positivity
    have h42 : 0 < (2 : ℝ)^m := by positivity
    have h4 : (1 : ℝ) / (2 : ℝ)^m < (1 : ℝ) / (2 : ℝ)^k := by
      calc (1 : ℝ) / (2 : ℝ)^m
        = (2 : ℝ)^k / ((2 : ℝ)^m * (2 : ℝ)^k) := by field_simp [h41.ne', h42.ne'] <;> ring
      _ < (2 : ℝ)^m / ((2 : ℝ)^m * (2 : ℝ)^k) := by gcongr
      _ = (1 : ℝ) / (2 : ℝ)^k := by field_simp [h41.ne', h42.ne'] <;> ring
    have h5 : ¬ (1 : ℝ) / (2 : ℝ)^k ≤ (1 : ℝ) / (2 : ℝ)^m := by
      exact not_le.mpr h4
    have h6 : (1 : ℝ) / (2 : ℝ)^k ≤ (1 : ℝ) / (2 : ℝ)^m := by
      simpa [dyadicDelta] using h
    exact h5 h6
  · intro h
    have h5 : (2 : ℝ)^m ≤ (2 : ℝ)^k := by gcongr <;> norm_num
    simp [dyadicDelta] <;> gcongr

/-- dyadicDelta product: dyadicDelta a * dyadicDelta b = dyadicDelta (a + b). -/
lemma dyadicDelta_mul (a b : ℕ) :
    dyadicDelta a * dyadicDelta b = dyadicDelta (a + b) := by
  simp [dyadicDelta, pow_add] <;> field_simp <;> ring

def offset (L : ℕ) (base : ℤ × ℤ) (idx : ℤ × ℤ) : ℤ × ℤ :=
  (base.1 * (2^L : ℤ) + idx.1, base.2 * (2^L : ℤ) + idx.2)

lemma offset_injective {L : ℕ} {base : ℤ × ℤ} :
    Function.Injective (offset L base) := by
  intro x y h
  have h1 : (offset L base x).1 = (offset L base y).1 := by rw [h]
  have h2 : (offset L base x).2 = (offset L base y).2 := by rw [h]
  simp [offset] at h1 h2
  exact Prod.ext (by omega) (by omega)

lemma parentBy_offset {L m' : ℕ} (hm' : m' ≤ L)
    (base : ℤ × ℤ) (idx : ℤ × ℤ) :
    parentBy m' (offset L base idx) = offset (L - m') base (parentBy m' idx) := by
  have hpow : (2^L : ℤ) = (2^m' : ℤ) * (2^(L - m') : ℤ) := by
    have h : m' + (L - m') = L := by omega
    have h' := pow_add (2 : ℤ) m' (L - m')
    rw [h] at h' <;> exact h'
  have hne : (2^m' : ℤ) ≠ 0 := by positivity
  have hdiv1 : ((base.1 * (2^L : ℤ) + idx.1) / (2^m' : ℤ)) =
      base.1 * (2^(L - m') : ℤ) + idx.1 / (2^m' : ℤ) := by
    have h : base.1 * (2^L : ℤ) = (base.1 * (2^(L - m') : ℤ)) * (2^m' : ℤ) := by
      rw [hpow] <;> ring
    rw [h]
    have h' : ((idx.1 + (base.1 * (2^(L - m') : ℤ)) * (2^m' : ℤ)) / (2^m' : ℤ)) =
        idx.1 / (2^m' : ℤ) + (base.1 * (2^(L - m') : ℤ)) :=
      Int.add_mul_ediv_right idx.1 (base.1 * (2^(L - m') : ℤ)) hne
    simpa [add_comm] using h'
  have hdiv2 : ((base.2 * (2^L : ℤ) + idx.2) / (2^m' : ℤ)) =
      base.2 * (2^(L - m') : ℤ) + idx.2 / (2^m' : ℤ) := by
    have h : base.2 * (2^L : ℤ) = (base.2 * (2^(L - m') : ℤ)) * (2^m' : ℤ) := by
      rw [hpow] <;> ring
    rw [h]
    have h' : ((idx.2 + (base.2 * (2^(L - m') : ℤ)) * (2^m' : ℤ)) / (2^m' : ℤ)) =
        idx.2 / (2^m' : ℤ) + (base.2 * (2^(L - m') : ℤ)) :=
      Int.add_mul_ediv_right idx.2 (base.2 * (2^(L - m') : ℤ)) hne
    simpa [add_comm] using h'
  ext <;> simp [parentBy, offset, hdiv1, hdiv2] <;> ring

lemma dyadicSquare_containment {m a_coarse : ℕ}
    (Q : DyadicSquare m) (g : ℤ × ℤ)
    (h1 : 0 ≤ g.1) (h2 : g.1 < (2 : ℤ)^a_coarse)
    (h3 : 0 ≤ g.2) (h4 : g.2 < (2 : ℤ)^a_coarse) :
    CombiningTheorem.dyadicSquare (dyadicDelta (m + a_coarse))
      (Q.i * (2^a_coarse : ℤ) + g.1) (Q.j * (2^a_coarse : ℤ) + g.2) ⊆
    CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j := by
  have hδ : dyadicDelta m = (2 : ℝ)^a_coarse * dyadicDelta (m + a_coarse) := by
    simp [dyadicDelta, pow_add] <;> field_simp <;> ring
  have hδ_pos : 0 < dyadicDelta (m + a_coarse) := dyadicDelta_pos (m + a_coarse)
  have h_pos1 : 0 ≤ (g.1 : ℝ) := by exact_mod_cast h1
  have h_lt1 : (g.1 : ℝ) < (2^a_coarse : ℝ) := by exact_mod_cast h2
  have h_pos2 : 0 ≤ (g.2 : ℝ) := by exact_mod_cast h3
  have h_lt2 : (g.2 : ℝ) < (2^a_coarse : ℝ) := by exact_mod_cast h4
  have h_le1 : (g.1 : ℝ) + 1 ≤ (2^a_coarse : ℝ) := by
    have h : g.1 + 1 ≤ (2^a_coarse : ℤ) := by linarith
    exact_mod_cast h
  have h_le2 : (g.2 : ℝ) + 1 ≤ (2^a_coarse : ℝ) := by
    have h : g.2 + 1 ≤ (2^a_coarse : ℤ) := by linarith
    exact_mod_cast h
  intro x hx
  simp only [CombiningTheorem.dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico] at hx ⊢
  rcases hx with ⟨⟨h_x1_lo, h_x1_hi⟩, ⟨h_x2_lo, h_x2_hi⟩⟩
  have h_cast1 : (↑(Q.i * 2 ^ a_coarse + g.1) : ℝ) = (Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ) := by
    simp [mul_add, add_mul] <;> ring
  have h_cast2 : (↑(Q.j * 2 ^ a_coarse + g.2) : ℝ) = (Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ) := by
    simp [mul_add, add_mul] <;> ring
  have h_x1_lo' : ((Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ)) * dyadicDelta (m + a_coarse) ≤ x 0 := by
    rw [h_cast1] at h_x1_lo; exact h_x1_lo
  have h_x1_hi' : x 0 < ((Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ) + 1) * dyadicDelta (m + a_coarse) := by
    have h_eq : (↑(Q.i * 2 ^ a_coarse + g.1) + 1 : ℝ) = (Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ) + 1 := by
      rw [h_cast1] <;> ring
    rw [h_eq] at h_x1_hi; exact h_x1_hi
  have h_x2_lo' : ((Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ)) * dyadicDelta (m + a_coarse) ≤ x 1 := by
    rw [h_cast2] at h_x2_lo; exact h_x2_lo
  have h_x2_hi' : x 1 < ((Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ) + 1) * dyadicDelta (m + a_coarse) := by
    have h_eq : (↑(Q.j * 2 ^ a_coarse + g.2) + 1 : ℝ) = (Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ) + 1 := by
      rw [h_cast2] <;> ring
    rw [h_eq] at h_x2_hi; exact h_x2_hi
  have h_lo1 : (Q.i : ℝ) * dyadicDelta m ≤ x 0 := by
    calc (Q.i : ℝ) * dyadicDelta m
      = (Q.i : ℝ) * ((2^a_coarse : ℝ) * dyadicDelta (m + a_coarse)) := by rw [hδ]
    _ = ((Q.i : ℝ) * (2^a_coarse : ℝ)) * dyadicDelta (m + a_coarse) := by ring
    _ ≤ ((Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ)) * dyadicDelta (m + a_coarse) := by gcongr <;> linarith
    _ ≤ x 0 := h_x1_lo'
  have h_hi1 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta m := by
    have h_bound : ((Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ) + 1) ≤ ((Q.i : ℝ) + 1) * (2^a_coarse : ℝ) := by
      have h : (g.1 : ℝ) + 1 ≤ (2^a_coarse : ℝ) := h_le1
      linarith
    calc x 0
      < ((Q.i : ℝ) * (2^a_coarse : ℝ) + (g.1 : ℝ) + 1) * dyadicDelta (m + a_coarse) := h_x1_hi'
    _ ≤ (((Q.i : ℝ) + 1) * (2^a_coarse : ℝ)) * dyadicDelta (m + a_coarse) := by gcongr <;> exact h_bound
    _ = ((Q.i : ℝ) + 1) * dyadicDelta m := by
      have h9 : ((Q.i : ℝ) + 1) * ((2^a_coarse : ℝ) * dyadicDelta (m + a_coarse)) = ((Q.i : ℝ) + 1) * dyadicDelta m := by
        rw [hδ]
      simpa [mul_assoc] using h9
  have h_lo2 : (Q.j : ℝ) * dyadicDelta m ≤ x 1 := by
    calc (Q.j : ℝ) * dyadicDelta m
      = (Q.j : ℝ) * ((2^a_coarse : ℝ) * dyadicDelta (m + a_coarse)) := by rw [hδ]
    _ = ((Q.j : ℝ) * (2^a_coarse : ℝ)) * dyadicDelta (m + a_coarse) := by ring
    _ ≤ ((Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ)) * dyadicDelta (m + a_coarse) := by gcongr <;> linarith
    _ ≤ x 1 := h_x2_lo'
  have h_hi2 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta m := by
    have h_bound : ((Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ) + 1) ≤ ((Q.j : ℝ) + 1) * (2^a_coarse : ℝ) := by
      have h : (g.2 : ℝ) + 1 ≤ (2^a_coarse : ℝ) := h_le2
      linarith
    calc x 1
      < ((Q.j : ℝ) * (2^a_coarse : ℝ) + (g.2 : ℝ) + 1) * dyadicDelta (m + a_coarse) := h_x2_hi'
    _ ≤ (((Q.j : ℝ) + 1) * (2^a_coarse : ℝ)) * dyadicDelta (m + a_coarse) := by gcongr <;> exact h_bound
    _ = ((Q.j : ℝ) + 1) * dyadicDelta m := by
      have h9 : ((Q.j : ℝ) + 1) * ((2^a_coarse : ℝ) * dyadicDelta (m + a_coarse)) = ((Q.j : ℝ) + 1) * dyadicDelta m := by
        rw [hδ]
      simpa [mul_assoc] using h9
  exact ⟨⟨h_lo1, h_hi1⟩, ⟨h_lo2, h_hi2⟩⟩

lemma setFromIndices_homothety {m a_last : ℕ} (k : ℕ) (hk : k = m + a_last)
    (Q : DyadicSquare m) (S : Finset (ℤ × ℤ)) :
    homothetyS (dyadicDelta m) Q.i Q.j ''
      setFromIndices (dyadicDelta k) (S.image (offset a_last (Q.i, Q.j))) =
    setFromIndices (dyadicDelta a_last) S := by
  let base : ℤ × ℤ := (Q.i, Q.j)
  have hnm : m ≤ k := by omega
  have h_kmm : k - m = a_last := by omega
  have h_main1 : ∀ idx ∈ S, homothetyS (dyadicDelta m) Q.i Q.j ''
        (CombiningTheorem.dyadicSquare (dyadicDelta k)
          (offset a_last base idx).1 (offset a_last base idx).2) =
      CombiningTheorem.dyadicSquare (dyadicDelta a_last) idx.1 idx.2 := by
    intro idx _
    let p : DyadicSquare k :=
      ⟨(offset a_last base idx).1, (offset a_last base idx).2⟩
    have h_p_toSet : p.toSet = CombiningTheorem.dyadicSquare (dyadicDelta k)
        (offset a_last base idx).1 (offset a_last base idx).2 := by
      ext x
      simp [DyadicSquare.toSet, CombiningTheorem.dyadicSquare, Set.mem_Ico] <;> tauto
    let q := InductionConfigurations.squareHomothety hnm Q p
    have h_q_i : q.i = idx.1 := by
      simp [InductionConfigurations.squareHomothety, q, p, offset,
        InductionConfigurations.refinementFactor, hk] <;> ring
    have h_q_j : q.j = idx.2 := by
      simp [InductionConfigurations.squareHomothety, q, p, offset,
        InductionConfigurations.refinementFactor, hk] <;> ring
    have h_img := squareHomothety_toSet hnm Q p
    rw [h_p_toSet] at h_img
    have h_q_toSet : q.toSet = CombiningTheorem.dyadicSquare (dyadicDelta a_last) idx.1 idx.2 := by
      ext x
      simp [DyadicSquare.toSet, CombiningTheorem.dyadicSquare, Set.mem_Ico, h_q_i, h_q_j, h_kmm] <;> tauto
    rw [h_q_toSet] at h_img
    exact h_img
  have h_union : homothetyS (dyadicDelta m) Q.i Q.j ''
      setFromIndices (dyadicDelta k) (S.image (offset a_last base)) =
      ⋃ idx ∈ S, homothetyS (dyadicDelta m) Q.i Q.j ''
        CombiningTheorem.dyadicSquare (dyadicDelta k)
          (offset a_last base idx).1 (offset a_last base idx).2 := by
    ext y
    simp only [setFromIndices, Set.mem_image, Set.mem_iUnion, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨idx, ⟨idx2, hidx2, rfl⟩, hx_sq⟩, rfl⟩
      exact ⟨idx2, hidx2, x, hx_sq, rfl⟩
    · rintro ⟨idx2, hidx2, x, hx_sq, rfl⟩
      exact ⟨x, ⟨offset a_last base idx2, ⟨idx2, hidx2, rfl⟩, hx_sq⟩, rfl⟩
  rw [h_union]
  have h_final : (⋃ idx ∈ S, homothetyS (dyadicDelta m) Q.i Q.j ''
        CombiningTheorem.dyadicSquare (dyadicDelta k)
          (offset a_last base idx).1 (offset a_last base idx).2) =
      ⋃ idx ∈ S, CombiningTheorem.dyadicSquare (dyadicDelta a_last) idx.1 idx.2 := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨idx, hidx, hx⟩
      exact ⟨idx, hidx, (h_main1 idx hidx) ▸ hx⟩
    · rintro ⟨idx, hidx, hx⟩
      exact ⟨idx, hidx, (h_main1 idx hidx).symm ▸ hx⟩
  rw [h_final] <;> rfl

lemma filtered_card_offset {L m_fine m_coarse : ℕ}
    (hm_fine : m_fine ≤ L) (hm_coarse : m_coarse ≤ L - m_fine)
    (base : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (g : ℤ × ℤ) :
    ((S.image (offset L base)).image (parentBy m_fine)).filter
      (fun idx => parentBy m_coarse idx = offset (L - m_fine - m_coarse) base g) =
    ((S.image (parentBy m_fine)).filter (fun idx => parentBy m_coarse idx = g)).image
      (offset (L - m_fine) base) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hpin, hfilter⟩
    rcases hpin with ⟨idx, ⟨idx2, hidx2, h_eq1⟩, rfl⟩
    let p' := parentBy m_fine idx2
    have h_p_eq : parentBy m_fine idx = offset (L - m_fine) base p' := by
      have h : parentBy m_fine idx = parentBy m_fine (offset L base idx2) := by congr <;> exact h_eq1.symm
      rw [h]
      exact parentBy_offset hm_fine base idx2
    have h_p'_in : p' ∈ S.image (parentBy m_fine) :=
      Finset.mem_image.mpr ⟨idx2, hidx2, rfl⟩
    have h6 := parentBy_offset hm_coarse base p'
    have h_filter' : parentBy m_coarse p' = g := by
      have h : parentBy m_coarse (parentBy m_fine idx) = offset (L - m_fine - m_coarse) base g := hfilter
      rw [h_p_eq] at h
      rw [h6] at h
      exact offset_injective h
    have h_p'_in' : ∃ (a : ℤ × ℤ), a ∈ S ∧ parentBy m_fine a = p' := by
      rw [Finset.mem_image] at h_p'_in
      exact h_p'_in
    exact ⟨p', ⟨h_p'_in', h_filter'⟩, h_p_eq.symm⟩
  · rintro ⟨p', ⟨hpin', hfilter'⟩, rfl⟩
    rcases hpin' with ⟨idx, hidx, h_eq1⟩
    have h5 := parentBy_offset hm_fine base idx
    have h6 := parentBy_offset hm_coarse base (parentBy m_fine idx)
    constructor
    · refine ⟨offset L base idx, ⟨idx, hidx, rfl⟩, ?_⟩
      rw [h5, h_eq1]
    · have h7 : parentBy m_coarse (parentBy m_fine idx) = g := by
        rw [h_eq1] <;> exact hfilter'
      have h_goal : parentBy m_coarse (offset (L - m_fine) base p') = offset (L - m_fine - m_coarse) base g := by
        have h8 : offset (L - m_fine) base p' = offset (L - m_fine) base (parentBy m_fine idx) := by rw [h_eq1]
        rw [h8, h6, h7]
      exact h_goal

/-- Reverse uniformity bridge through Q-homothety. -/
lemma isUniformAtScales_to_rangeUniformity_Q
    {n n_fine k : ℕ} (hn_fine : n_fine + 1 = n)
    (P : Set Plane) (Δ : Fin (n + 1) → ℝ) (N : Fin n → ℕ)
    (h_uniform : IsUniformAtScales P n Δ N)
    (m : ℕ) (Q : DyadicSquare m)
    (hΔ1_eq : Δ 1 = dyadicDelta m)
    (hΔk_eq : Δ (Fin.last n) = dyadicDelta k)
    (a : Fin (n_fine + 1) → ℕ)
    (ha_spec : ∀ (i : Fin (n_fine + 1)),
      Δ (⟨i.val + 1, by omega⟩ : Fin (n + 1)) / Δ 1 = dyadicDelta (a i))
    (ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (ha_last_max : ∀ i, a i ≤ a (Fin.last n_fine))
    (S_full_norm : Finset (ℤ × ℤ))
    (hS_nonempty : S_full_norm.Nonempty)
    (hP_Q_eq : homothetyS (Δ 1) Q.i Q.j '' (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j)
                    = setFromIndices (dyadicDelta (a (Fin.last n_fine))) S_full_norm)
    (h_unit_S : ∀ idx ∈ S_full_norm, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
                 idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧
                 idx.2 < (2 : ℤ)^(a (Fin.last n_fine))) :
    RangeUniformityProp n_fine a S_full_norm (fun j' : Fin n_fine =>
      N ⟨j'.val + 1, by omega⟩) := by
  set a_last : ℕ := a (Fin.last n_fine) with ha_last_def
  have hδ1_pos : 0 < Δ 1 := by
    rw [hΔ1_eq] <;> exact dyadicDelta_pos m
  have h_fin_eq : (Fin.last n : Fin (n + 1)) =
      ⟨(Fin.last n_fine : ℕ) + 1, by omega⟩ := by
    apply Fin.ext <;> simp [hn_fine, Fin.last] <;> omega
  have h1 : Δ (Fin.last n) / Δ 1 = dyadicDelta a_last := by
    rw [h_fin_eq]
    exact ha_spec (Fin.last n_fine)
  have h4 : Δ (Fin.last n) / Δ 1 ≤ 1 := by
    rw [h1]
    exact dyadicDelta_le_one a_last
  have h6 : Δ (Fin.last n) ≤ Δ 1 := by
    calc Δ (Fin.last n)
      = (Δ (Fin.last n) / Δ 1) * Δ 1 := by field_simp [hδ1_pos.ne'] <;> ring
    _ ≤ 1 * Δ 1 := by gcongr
    _ = Δ 1 := by ring
  have h7 : dyadicDelta k ≤ dyadicDelta m := by
    rw [hΔk_eq, hΔ1_eq] at h6
    exact h6
  have h3 : m ≤ k := dyadicDelta_le_iff.mp h7
  have h2 : dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := by
    have h4 : m + (k - m) = k := by omega
    have h5 : (2 : ℝ)^k = (2 : ℝ)^m * (2 : ℝ)^(k - m) := by
      rw [← pow_add, h4]
    simp [dyadicDelta, h5] <;> field_simp <;> ring
  have h1' : dyadicDelta k / dyadicDelta m = dyadicDelta a_last := by
    rw [hΔk_eq, hΔ1_eq] at h1
    exact h1
  rw [h2] at h1'
  have h5 : dyadicDelta (k - m) = dyadicDelta a_last := h1'
  have h6' : (1 : ℝ) / (2 : ℝ)^(k - m) = (1 : ℝ) / (2 : ℝ)^a_last := by
    simpa [dyadicDelta] using h5
  have h_pos1 : 0 < (2 : ℝ)^(k - m) := by positivity
  have h_pos2 : 0 < (2 : ℝ)^a_last := by positivity
  have h7' : (2 : ℝ)^(k - m) = (2 : ℝ)^a_last := by
    calc (2 : ℝ)^(k - m)
      = 1 / ((1 : ℝ) / (2 : ℝ)^(k - m)) := by field_simp [h_pos1.ne'] <;> ring
    _ = 1 / ((1 : ℝ) / (2 : ℝ)^a_last) := by rw [h6']
    _ = (2 : ℝ)^a_last := by field_simp [h_pos2.ne'] <;> ring
  have h8 : (k - m) = a_last := by
    have h9 : (2 : ℕ)^(k - m) = (2 : ℕ)^a_last := by exact_mod_cast h7'
    exact Nat.pow_right_injective (by norm_num) h9
  have h_k_eq : k = m + a_last := by omega
  let base : ℤ × ℤ := (Q.i, Q.j)
  let S_global : Finset (ℤ × ℤ) := S_full_norm.image (offset a_last base)
  let lower : Plane := WithLp.toLp (2 : ENNReal)
    (fun k : Fin 2 => if k = 0 then (Q.i : ℝ) * Δ 1 else (Q.j : ℝ) * Δ 1)
  have h_hom_inj : Function.Injective (homothetyS (Δ 1) Q.i Q.j) := by
    intro x y h
    have h9 : (1 / Δ 1 : ℝ) ≠ 0 := by positivity
    have h_eq : (1 / Δ 1 : ℝ) • (x - lower) = (1 / Δ 1 : ℝ) • (y - lower) := by
      simpa [homothetyS, lower] using h
    have h10 : (1 / Δ 1 : ℝ) • ((x - lower) - (y - lower)) = 0 := by
      simpa [smul_sub] using sub_eq_zero.mpr h_eq
    have h11 : (1 / Δ 1 : ℝ) = 0 ∨ (x - lower) - (y - lower) = 0 := by
      simpa [smul_eq_zero] using h10
    have h12 : (x - lower) - (y - lower) = 0 := by
      rcases h11 with (h11 | h11)
      · exfalso; exact h9 h11
      · exact h11
    have h13 : x - lower = y - lower := by
      simpa [sub_eq_zero] using h12
    have hxy : x = y := by
      calc x
        = x - lower + lower := by abel
      _ = y - lower + lower := by rw [h13]
      _ = y := by abel
    exact hxy
  have hP_Q_set : P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j =
      setFromIndices (dyadicDelta k) S_global := by
    have h_img : homothetyS (Δ 1) Q.i Q.j '' (setFromIndices (dyadicDelta k) S_global) =
        setFromIndices (dyadicDelta a_last) S_full_norm := by
      rw [hΔ1_eq]
      exact setFromIndices_homothety k h_k_eq Q S_full_norm
    have h_eq1 : homothetyS (Δ 1) Q.i Q.j '' (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) =
        homothetyS (Δ 1) Q.i Q.j '' (setFromIndices (dyadicDelta k) S_global) := by
      rw [hP_Q_eq, h_img]
    apply Set.ext
    intro x
    have h_iff1 : x ∈ (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) ↔
        homothetyS (Δ 1) Q.i Q.j x ∈ homothetyS (Δ 1) Q.i Q.j '' (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) := by
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, h_eq⟩
        have h_yx : y = x := h_hom_inj h_eq
        rw [h_yx] at hy
        exact hy
    have h_iff2 : x ∈ setFromIndices (dyadicDelta k) S_global ↔
        homothetyS (Δ 1) Q.i Q.j x ∈ homothetyS (Δ 1) Q.i Q.j '' (setFromIndices (dyadicDelta k) S_global) := by
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, h_eq⟩
        have h_yx : y = x := h_hom_inj h_eq
        rw [h_yx] at hy
        exact hy
    rw [h_iff1, h_iff2, h_eq1]
  have hN_pos : ∀ j : Fin n, 1 ≤ N j := h_uniform.2.1
  have h_range : ∀ (j' : Fin n_fine) (g : ℤ × ℤ),
      let m_fine := a_last - a (Fin.succ j')
      let m_coarse := a (Fin.succ j') - a j'.castSucc
      let fineSquares := S_full_norm.image (parentBy m_fine)
      let count := (fineSquares.filter (fun idx => parentBy m_coarse idx = g)).card
      count = 0 ∨ (N ⟨j'.val + 1, by omega⟩ ≤ count ∧ count < 2 * N ⟨j'.val + 1, by omega⟩) := by
    intro j' g
    set a_coarse : ℕ := a j'.castSucc with ha_coarse_def
    set a_fine : ℕ := a (Fin.succ j') with ha_fine_def
    set m_fine : ℕ := a_last - a_fine with hm_fine_def
    set m_coarse : ℕ := a_fine - a_coarse with hm_coarse_def
    set j_orig : Fin n := ⟨j'.val + 1, by omega⟩ with hj_orig_def
    have h_coarse_le_fine : a_coarse ≤ a_fine := ha_mono j'
    have h_fine_le_last : a_fine ≤ a_last := ha_last_max (Fin.succ j')
    have h_m_fine_le_last : m_fine ≤ a_last := by omega
    have h_m_coarse_le : m_coarse ≤ a_last - m_fine := by omega
    set g_global : ℤ × ℤ := offset a_coarse base g with hg_global_def
    have h_idx_succ : (Fin.succ j_orig : Fin (n + 1)) = ⟨j'.val + 2, by omega⟩ := by
      apply Fin.ext <;> simp [hj_orig_def] <;> omega
    have h_idx_cast : (j_orig.castSucc : Fin (n + 1)) = ⟨j'.val + 1, by omega⟩ := by
      apply Fin.ext <;> simp [hj_orig_def] <;> omega
    have h_scale_fine : Δ (Fin.succ j_orig) = dyadicDelta (m + a_fine) := by
      rw [h_idx_succ]
      have h1 := ha_spec (Fin.succ j')
      have h5 : 0 < Δ 1 := hδ1_pos
      have h3 : Δ (⟨j'.val + 2, by omega⟩ : Fin (n + 1)) = Δ 1 * dyadicDelta a_fine := by
        field_simp [h5.ne'] at h1 ⊢ <;> exact h1
      rw [h3, hΔ1_eq, dyadicDelta_mul m a_fine]
    have h_scale_coarse : Δ j_orig.castSucc = dyadicDelta (m + a_coarse) := by
      rw [h_idx_cast]
      have h1 := ha_spec j'.castSucc
      have h5 : 0 < Δ 1 := hδ1_pos
      have h3 : Δ (⟨j'.val + 1, by omega⟩ : Fin (n + 1)) = Δ 1 * dyadicDelta a_coarse := by
        field_simp [h5.ne'] at h1 ⊢ <;> exact h1
      rw [h3, hΔ1_eq, dyadicDelta_mul m a_coarse]
    by_cases h_in_bounds : (0 ≤ g.1 ∧ g.1 < (2 : ℤ)^a_coarse ∧ 0 ≤ g.2 ∧ g.2 < (2 : ℤ)^a_coarse)
    · -- In bounds
      have h_g1 : g_global.1 = Q.i * (2^a_coarse : ℤ) + g.1 := by
        simp [hg_global_def, offset] <;> ring
      have h_g2 : g_global.2 = Q.j * (2^a_coarse : ℤ) + g.2 := by
        simp [hg_global_def, offset] <;> ring
      have h_square_subset_Q : CombiningTheorem.dyadicSquare (dyadicDelta (m + a_coarse)) g_global.1 g_global.2 ⊆
          CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j := by
        rw [h_g1, h_g2]
        exact dyadicSquare_containment Q g h_in_bounds.1 h_in_bounds.2.1 h_in_bounds.2.2.1 h_in_bounds.2.2.2
      have h_inter_eq : (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) ∩
          CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2 =
          P ∩ CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2 := by
        ext x
        simp only [Set.mem_inter_iff]
        constructor
        · rintro ⟨⟨hxP, _⟩, hx_sq⟩
          exact ⟨hxP, hx_sq⟩
        · rintro ⟨hxP, hx_sq⟩
          have h_x : x ∈ CombiningTheorem.dyadicSquare (dyadicDelta (m + a_coarse)) g_global.1 g_global.2 := by
            rw [←h_scale_coarse] <;> exact hx_sq
          have h_in_Q : x ∈ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j := by
            rw [hΔ1_eq]
            exact h_square_subset_Q h_x
          exact ⟨⟨hxP, h_in_Q⟩, hx_sq⟩
      have h_bridge1 : (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) ∩
          CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2 =
          setFromIndices (dyadicDelta k) S_global ∩
          CombiningTheorem.dyadicSquare (dyadicDelta (m + a_coarse)) g_global.1 g_global.2 := by
        ext x
        simp only [Set.mem_inter_iff]
        constructor
        · rintro ⟨h1, h2⟩
          have h1' : x ∈ setFromIndices (dyadicDelta k) S_global := by
            rw [←hP_Q_set] <;> exact h1
          have h2' : x ∈ CombiningTheorem.dyadicSquare (dyadicDelta (m + a_coarse)) g_global.1 g_global.2 := by
            rw [←h_scale_coarse] <;> exact h2
          exact ⟨h1', h2'⟩
        · rintro ⟨h1, h2⟩
          have h1' : x ∈ P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j := by
            rw [hP_Q_set] <;> exact h1
          have h2' : x ∈ CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2 := by
            rw [h_scale_coarse] <;> exact h2
          exact ⟨h1', h2'⟩
      have h_bridge : dyadicSquareCount (Δ (Fin.succ j_orig))
            ((P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) ∩
              CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2) =
          ↑(((S_global.image (parentBy m_fine)).filter
            (fun idx => parentBy m_coarse idx = g_global)).card) := by
        rw [h_scale_fine, h_bridge1]
        have h_mf : m_fine = k - (m + a_fine) := by omega
        have h_mc : m_coarse = (m + a_fine) - (m + a_coarse) := by omega
        simp only [h_mf, h_mc]
        exact OSUniformisation.dyadicSquareCount_setFromIndices_inter k (m + a_fine) (m + a_coarse)
          (by omega) (by omega) S_global g_global
      have h_card_eq : ((S_global.image (parentBy m_fine)).filter
            (fun idx => parentBy m_coarse idx = g_global)).card =
          ((S_full_norm.image (parentBy m_fine)).filter
            (fun idx => parentBy m_coarse idx = g)).card := by
        have h9 : g_global = offset (a_last - m_fine - m_coarse) base g := by
          simp [hg_global_def, offset, hm_fine_def, hm_coarse_def] <;> omega
        rw [h9]
        have h_eq_set := filtered_card_offset h_m_fine_le_last h_m_coarse_le base S_full_norm g
        rw [h_eq_set]
        have h_inj : Set.InjOn (offset (a_last - m_fine) base)
            (↑((S_full_norm.image (parentBy m_fine)).filter
              (fun idx => parentBy m_coarse idx = g))) := by
          intro x _ y _ h
          exact offset_injective h
        rw [Finset.card_image_of_injOn h_inj]
      have h3 := h_uniform.2.2 j_orig g_global.1 g_global.2
      have h_uniform_count : dyadicSquareCount (Δ (Fin.succ j_orig))
          (P ∩ CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2) = 0 ∨
          (↑(N j_orig) ≤ dyadicSquareCount (Δ (Fin.succ j_orig))
            (P ∩ CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2) ∧
           dyadicSquareCount (Δ (Fin.succ j_orig))
            (P ∩ CombiningTheorem.dyadicSquare (Δ j_orig.castSucc) g_global.1 g_global.2) < ↑(2 * N j_orig)) := by
        exact h3
      rw [←h_inter_eq] at h_uniform_count
      rw [h_bridge, h_card_eq] at h_uniform_count
      rcases h_uniform_count with (h3 | h3)
      · exact Or.inl (Nat.cast_eq_zero.mp h3)
      · exact Or.inr ⟨Nat.cast_le.mp h3.1, Nat.cast_lt.mp h3.2⟩
    · -- Out of bounds
      have h_out : g.1 < 0 ∨ g.1 ≥ (2 : ℤ)^a_coarse ∨ g.2 < 0 ∨ g.2 ≥ (2 : ℤ)^a_coarse := by
        by_contra h
        push Not at h
        exact h_in_bounds ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
      have h_empty : ((S_full_norm.image (parentBy m_fine)).filter
          (fun idx => parentBy m_coarse idx = g)) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨⟨idx, hidx, rfl⟩, h_eq⟩
          have h_pos_mf : 0 < (2^m_fine : ℤ) := by positivity
          have h_pos_mc : 0 < (2^m_coarse : ℤ) := by positivity
          have h_sum : m_fine + m_coarse = a_last - a_coarse := by omega
          have h9 : 0 ≤ idx.1 := (h_unit_S idx hidx).1
          have h10 : idx.1 < (2 : ℤ)^a_last := (h_unit_S idx hidx).2.2.1
          have h9' : 0 ≤ idx.2 := (h_unit_S idx hidx).2.1
          have h10' : idx.2 < (2 : ℤ)^a_last := (h_unit_S idx hidx).2.2.2
          have h_ediv1 : (parentBy m_coarse (parentBy m_fine idx)).1 =
              idx.1 / ((2^m_fine : ℤ) * (2^m_coarse : ℤ)) := by
            simp [parentBy, Int.ediv_ediv] <;> ring
          have h_ediv2 : (parentBy m_coarse (parentBy m_fine idx)).2 =
              idx.2 / ((2^m_fine : ℤ) * (2^m_coarse : ℤ)) := by
            simp [parentBy, Int.ediv_ediv] <;> ring
          have h_prod : (2^a_coarse : ℤ) * ((2^m_fine : ℤ) * (2^m_coarse : ℤ)) = (2 : ℤ)^a_last := by
            have h13 : m_fine + m_coarse + a_coarse = a_last := by omega
            calc (2^a_coarse : ℤ) * ((2^m_fine : ℤ) * (2^m_coarse : ℤ))
              = (2^a_coarse : ℤ) * (2 : ℤ)^(m_fine + m_coarse) := by rw [← pow_add] <;> ring
            _ = (2 : ℤ)^(a_coarse + (m_fine + m_coarse)) := by rw [← pow_add]
            _ = (2 : ℤ)^a_last := by rw [show a_coarse + (m_fine + m_coarse) = a_last by omega]
          have h_b1 : 0 ≤ (parentBy m_coarse (parentBy m_fine idx)).1 := by
            rw [h_ediv1]
            apply Int.ediv_nonneg <;> positivity
          have h_b2 : (parentBy m_coarse (parentBy m_fine idx)).1 < (2 : ℤ)^a_coarse := by
            rw [h_ediv1]
            let d : ℤ := (2^m_fine : ℤ) * (2^m_coarse : ℤ)
            have hd_pos : 0 < d := by positivity
            by_contra h
            push Not at h
            have h15 : (2^a_coarse : ℤ) ≤ idx.1 / d := h
            have h16 : (2^a_coarse : ℤ) * d ≤ idx.1 := by
              calc (2^a_coarse : ℤ) * d
                ≤ (idx.1 / d) * d := by gcongr
              _ = d * (idx.1 / d) := by ring
              _ ≤ idx.1 := by
                have h_eq : d * (idx.1 / d) + (idx.1 % d) = idx.1 := by exact Int.mul_ediv_add_emod idx.1 d
                have h_nonneg : 0 ≤ idx.1 % d := Int.emod_nonneg idx.1 (by positivity)
                linarith
            rw [h_prod] at h16
            omega
          have h_b3 : 0 ≤ (parentBy m_coarse (parentBy m_fine idx)).2 := by
            rw [h_ediv2]
            apply Int.ediv_nonneg <;> positivity
          have h_b4 : (parentBy m_coarse (parentBy m_fine idx)).2 < (2 : ℤ)^a_coarse := by
            rw [h_ediv2]
            let d : ℤ := (2^m_fine : ℤ) * (2^m_coarse : ℤ)
            have hd_pos : 0 < d := by positivity
            by_contra h
            push Not at h
            have h15 : (2^a_coarse : ℤ) ≤ idx.2 / d := h
            have h16 : (2^a_coarse : ℤ) * d ≤ idx.2 := by
              calc (2^a_coarse : ℤ) * d
                ≤ (idx.2 / d) * d := by gcongr
              _ = d * (idx.2 / d) := by ring
              _ ≤ idx.2 := by
                have h_eq : d * (idx.2 / d) + (idx.2 % d) = idx.2 := by exact Int.mul_ediv_add_emod idx.2 d
                have h_nonneg : 0 ≤ idx.2 % d := Int.emod_nonneg idx.2 (by positivity)
                linarith
            rw [h_prod] at h16
            omega
          rw [h_eq] at h_b1 h_b2 h_b3 h_b4
          rcases h_out with (h | h | h | h) <;> omega
        · intro h
          simpa using h
      have h_count_zero : ((S_full_norm.image (parentBy m_fine)).filter
          (fun idx => parentBy m_coarse idx = g)).card = 0 := by
        rw [h_empty]
        exact Finset.card_empty
      exact Or.inl h_count_zero
  exact ⟨hS_nonempty, fun j' => hN_pos ⟨j'.val + 1, by omega⟩, h_range⟩

/-- Equation-(89) logarithmic absorption. -/
lemma equation89_log_absorption
    {δ δbar τ C_P C_n : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P) (hCn_ge1 : 1 ≤ C_n)
    (h_scale_sep : δbar ≤ δ^τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n))) :
    (Real.log (1 / δ)) ^ C_P ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) := by
  have h1 : 0 < Real.log (1 / δ) := by
    have h11 : 1 < 1 / δ := by apply one_lt_one_div hδ_pos; exact hδ_lt_one
    exact Real.log_pos h11
  have h2 : 0 < Real.log (1 / δbar) := by
    have h21 : 1 < 1 / δbar := by apply one_lt_one_div hδbar_pos; exact hδbar_lt_one
    exact Real.log_pos h21
  have h3 : 1 < Real.log (1 / δbar) := by
    have h6 : τ ^ (-(C_P + C_n)) > 1 := by
      have h7 : τ ^ (-(C_P + C_n)) = (1 / τ) ^ (C_P + C_n) := by
        have h8 : τ ^ (-(C_P + C_n)) = (τ ^ (C_P + C_n))⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h8]
        have h9 : (τ ^ (C_P + C_n))⁻¹ = (1 / τ) ^ (C_P + C_n) := by
          rw [← Real.inv_rpow (by linarith)] <;> ring_nf
        exact h9
      rw [h7]
      have h10 : 1 < 1 / τ := by apply one_lt_one_div hτ_pos; exact hτ_lt_one
      have h11 : 0 < C_P + C_n := by linarith
      exact Real.one_lt_rpow h10 h11
    linarith [h_small]
  have h_step1 : Real.log (1 / δ) ≤ (1 / τ) * Real.log (1 / δbar) := by
    have h9 : 1 / δbar ≥ (1 / δ) ^ τ := by
      have h10 : 0 < δ ^ τ := by positivity
      have h11 : 1 / δbar ≥ 1 / δ ^ τ := by gcongr
      have h12 : 1 / δ ^ τ = (1 / δ) ^ τ := by
        have h13 : 1 / δ ^ τ = (δ ^ τ)⁻¹ := by simp
        rw [h13]
        have h14 : (δ ^ τ)⁻¹ = (1 / δ) ^ τ := by
          rw [← Real.inv_rpow (by linarith)]
          <;> simp [one_div]
        exact h14
      rw [h12] at h11; exact h11
    have h13 : Real.log (1 / δbar) ≥ Real.log ((1 / δ) ^ τ) := Real.log_le_log (by positivity) h9
    have h14 : Real.log ((1 / δ) ^ τ) = τ * Real.log (1 / δ) := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h14] at h13
    have h15 : (1 / τ) * Real.log (1 / δbar) ≥ Real.log (1 / δ) := by
      calc (1 / τ) * Real.log (1 / δbar)
        ≥ (1 / τ) * (τ * Real.log (1 / δ)) := by gcongr
      _ = Real.log (1 / δ) := by field_simp [hτ_pos.ne'] <;> ring
    exact h15
  have h_step2 : (1 / τ) ^ C_P ≤ (Real.log (1 / δbar)) ^ (2 * C_n) := by
    have h4 : Real.log (Real.log (1 / δbar)) ≥ Real.log (τ ^ (-(C_P + C_n))) :=
      Real.log_le_log (by positivity) h_small
    have h5 : Real.log (τ ^ (-(C_P + C_n))) = (C_P + C_n) * Real.log (1 / τ) := by
      have h6 : Real.log (τ ^ (-(C_P + C_n))) = (-(C_P + C_n)) * Real.log τ := by
        rw [Real.log_rpow (by linarith)] <;> ring
      rw [h6]
      have h7 : Real.log τ = -Real.log (1 / τ) := by
        rw [Real.log_div (by norm_num) hτ_pos.ne'] <;> simp
      rw [h7] <;> ring
    rw [h5] at h4
    have h6 : 2 * C_n * Real.log (Real.log (1 / δbar)) ≥ C_P * Real.log (1 / τ) := by
      have h7 : 2 * C_n * (C_P + C_n) ≥ C_P := by nlinarith [hCP, hCn_ge1]
      have h8 : 0 < Real.log (1 / τ) := by
        have h9 : 1 < 1 / τ := by apply one_lt_one_div hτ_pos; exact hτ_lt_one
        exact Real.log_pos h9
      nlinarith [h4, h8]
    have h9 : (Real.log (1 / δbar)) ^ (2 * C_n) ≥ (1 / τ) ^ C_P := by
      have h10 : 0 < Real.log (1 / δbar) := by linarith
      have h11 : 0 < 1 / τ := by positivity
      have h12 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) =
          2 * C_n * Real.log (Real.log (1 / δbar)) := by
        rw [Real.log_rpow (by linarith [h3])] <;> ring
      have h13 : Real.log ((1 / τ) ^ C_P) = C_P * Real.log (1 / τ) := by
        rw [Real.log_rpow (by positivity)] <;> ring
      have h14 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) ≥ Real.log ((1 / τ) ^ C_P) := by
        rw [h12, h13]; exact h6
      by_contra h15
      have h16 : (Real.log (1 / δbar)) ^ (2 * C_n) < (1 / τ) ^ C_P := by linarith
      have h17 : 0 < (Real.log (1 / δbar)) ^ (2 * C_n) := by positivity
      have h18 : Real.log ((Real.log (1 / δbar)) ^ (2 * C_n)) < Real.log ((1 / τ) ^ C_P) :=
        Real.log_lt_log h17 h16
      linarith
    exact h9
  have h_step3 : (Real.log (1 / δ)) ^ C_P ≤
      (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := by
    have h19 : Real.log (1 / δ) ≤ (1 / τ) * Real.log (1 / δbar) := h_step1
    have h20 : (Real.log (1 / δ)) ^ C_P ≤ ((1 / τ) * Real.log (1 / δbar)) ^ C_P := by
      gcongr <;> linarith
    have h21 : ((1 / τ) * Real.log (1 / δbar)) ^ C_P =
        (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := by
      rw [Real.mul_rpow] <;> positivity
    rw [h21] at h20; exact h20
  calc (Real.log (1 / δ)) ^ C_P
    ≤ (1 / τ) ^ C_P * (Real.log (1 / δbar)) ^ C_P := h_step3
  _ = (Real.log (1 / δbar)) ^ C_P * (1 / τ) ^ C_P := by ring
  _ ≤ (Real.log (1 / δbar)) ^ C_P * (Real.log (1 / δbar)) ^ (2 * C_n) := by gcongr <;> linarith [h2, h3]
  _ = (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) := by
    rw [← Real.rpow_add] <;> linarith [h2, h3]

lemma equation89_cbetween_normal
    {δ δbar τ C_P C_n ε_N ratio : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P) (hCn_ge1 : 1 ≤ C_n)
    (hεN : 0 < ε_N) (h_ratio_nonneg : 0 ≤ ratio)
    (h_scale_sep : δbar ≤ δ^τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n)))
    (C_between : ℝ)
    (h_coarse_bound : C_between ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_N) :
    C_between ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_N := by
  have h_log : (Real.log (1 / δ)) ^ C_P ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) :=
    equation89_log_absorption hδ_pos hδ_lt_one hδbar_pos hδbar_lt_one
      hτ_pos hτ_lt_one hCP hCn_ge1 h_scale_sep h_small
  calc C_between
    ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_N := h_coarse_bound
  _ ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_N := by
    exact mul_le_mul_of_nonneg_right h_log (Real.rpow_nonneg h_ratio_nonneg ε_N)

lemma equation89_cbetween_good
    {δ δbar τ C_P C_n ε_G ratio : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (hCP : 1 ≤ C_P) (hCn_ge1 : 1 ≤ C_n)
    (hεG : 0 < ε_G) (h_ratio_nonneg : 0 ≤ ratio)
    (h_scale_sep : δbar ≤ δ^τ)
    (h_small : Real.log (1 / δbar) ≥ τ ^ (-(C_P + C_n)))
    (C_between : ℝ)
    (h_coarse_bound : C_between ≤ (Real.log (1 / δ)) ^ C_P * ratio ^ ε_G) :
    C_between ≤ (Real.log (1 / δbar)) ^ (C_P + 2 * C_n) * ratio ^ ε_G :=
  equation89_cbetween_normal hδ_pos hδ_lt_one hδbar_pos hδbar_lt_one
    hτ_pos hτ_lt_one hCP hCn_ge1 hεG h_ratio_nonneg h_scale_sep h_small C_between h_coarse_bound

/-- Construct a fine `CombiningConfig` from the coarse config and B1 bridge data.

    Parameters:
    - n_fine: number of fine scales (coarse has n_fine + 1 scales)
    - coarse CombiningConfig at n_fine + 1 scales
    - B1 bridge output for fine config
    - Normalized scale definitions

    h_uniform is proved via the Q-homothety uniformity bridge.
    h_C_between_normal and h_C_between_good are supplied by the inductive step context. -/
lemma fine_config_from_coarse
    {n_fine : ℕ}
    {s t τ ε_G η lam ε_N C_P : ℝ}
    {k m : ℕ} (hnm : m ≤ k)
    {M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin (n_fine + 2) → ℝ}
    {scaleClass : Fin (n_fine + 1) → ScaleClass}
    {N : Fin (n_fine + 1) → ℕ}
    {C_between : Fin (n_fine + 1) → ℝ}
    (hcfg : CombiningConfig s t τ (n_fine + 1) ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    -- B1 bridge data
    {Q : DyadicSquare m}
    {MQ : ℕ} (hMQ_pos : 0 < MQ)
    {lam_tail : ℝ}
    {fineConfig : CTNiceConfiguration (k - m) s (Real.rpow (dyadicDelta (k - m)) (-lam_tail)) MQ}
    (hfine_pointSet_eq : fineConfig.pointSet =
      homothetyS (dyadicDelta m) Q.i Q.j '' (config.pointSet ∩ BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j))
    -- Unit square property for fine config
    (h_squares_unit : ∀ (p : DyadicSquare (k - m)), p ∈ fineConfig.P₀ →
      0 ≤ p.i ∧ p.i < (2 : ℤ)^(k - m) ∧ 0 ≤ p.j ∧ p.j < (2 : ℤ)^(k - m))
    (hP0_nonempty : fineConfig.P₀.Nonempty)
    -- Fine parameters
    (C_P_fine : ℝ)
    (hlam_tail_pos : 0 < lam_tail)
    (hCP_fine : 1 ≤ C_P_fine)
    -- Normalized scales
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1)
    (scaleClass' : Fin n_fine → ScaleClass)
    (hscaleClass'_def : ∀ j, scaleClass' j = scaleClass (Fin.succ j))
    (N' : Fin n_fine → ℕ)
    (hN'_def : ∀ j, N' j = N (Fin.succ j))
    (C_between' : Fin n_fine → ℝ)
    (hC_between'_def : ∀ j, C_between' j = C_between (Fin.succ j))
    -- Coarse scale identification
    (hΔ1_eq : Δ 1 = dyadicDelta m)
    (hδbar_eq : Δ (Fin.last (n_fine + 1)) / Δ 1 = dyadicDelta (k - m))
    -- τ positivity
    (hτ_pos : 0 < τ)
    -- Equation (89) C_between transfer hypotheses
    (C_n : ℝ) (hCn_ge1 : 1 ≤ C_n)
    (hCP : 1 ≤ C_P)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (hτ_lt_one : τ < 1)
    (hεN_pos : 0 < ε_N)
    (hεG_pos : 0 < ε_G)
    (hk_pos : 0 < k)
    (hm_lt_k : m < k)
    (h_scale_sep : dyadicDelta (k - m) ≤ (dyadicDelta k)^τ)
    (h_small : Real.log (1 / dyadicDelta (k - m)) ≥ τ ^ (-(C_P + C_n))) :
    CombiningConfig s t τ n_fine ε_G η lam_tail ε_N C_P_fine C_between'
      (k - m) MQ fineConfig Δ' scaleClass' N' := by
  let δbar : ℝ := dyadicDelta (k - m)
  let shift : Fin n_fine → Fin (n_fine + 1) := fun j => Fin.succ j

  -- Scale normalization properties
  have h_scale_norm := scale_normalization_properties
    (n_fine := n_fine) Δ
    hcfg.hΔ_pos hcfg.hΔ_dyadic hcfg.hΔ_strict hcfg.hΔ_start
    (dyadicDelta k) hcfg.hΔ_end δbar (by rw [hδbar_eq])
    τ hτ_pos scaleClass hcfg.h_scale_ratio

  -- Extract components
  have hΔ'_pos : ∀ i : Fin (n_fine + 1), 0 < Δ' i := by
    intro i; rw [hΔ'_def]; exact h_scale_norm.1 i
  have hΔ'_dyadic : ∀ i : Fin (n_fine + 1), Δ' i ∈ dyadicScales := by
    intro i; rw [hΔ'_def]; exact h_scale_norm.2.1 i
  have hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc := by
    intro j; rw [hΔ'_def (Fin.succ j), hΔ'_def j.castSucc]; exact h_scale_norm.2.2.1 j
  have hΔ'_start : Δ' 0 = 1 := by
    rw [hΔ'_def 0]; exact h_scale_norm.2.2.2.1
  have h_scale_ratio' : ∀ j : Fin n_fine,
      ¬(scaleClass' j).isBad →
        Δ' (Fin.succ j) / Δ' j.castSucc ≤ Real.rpow δbar τ := by
    intro j hnotbad
    rw [hΔ'_def (Fin.succ j), hΔ'_def j.castSucc]
    have h : ¬(scaleClass (shift j)).isBad := by
      rw [hscaleClass'_def j] at *; exact hnotbad
    exact h_scale_norm.2.2.2.2 j h

  -- hΔ_end
  have hΔ'_end : Δ' (Fin.last n_fine) = dyadicDelta (k - m) := by
    rw [hΔ'_def (Fin.last n_fine)]
    have h1 : Fin.succ (Fin.last n_fine) = Fin.last (n_fine + 1) := by
      apply Fin.ext; simp [Fin.last] <;> omega
    rw [h1]
    exact hδbar_eq

  -- Restrict scales to indices 1..n_fine+1 for between-scales transfer
  let Δ_r : Fin (n_fine + 1) → ℝ := fun i => Δ (Fin.succ i)
  let scaleClass_r : Fin n_fine → ScaleClass := fun j => scaleClass (Fin.succ j)
  let C_between_r : Fin n_fine → ℝ := fun j => C_between (Fin.succ j)

  have hΔ_r_pos : ∀ i : Fin (n_fine + 1), 0 < Δ_r i := by
    intro i; exact hcfg.hΔ_pos (Fin.succ i)
  have hΔ_r_dyadic : ∀ i : Fin (n_fine + 1), Δ_r i ∈ dyadicScales := by
    intro i; exact hcfg.hΔ_dyadic (Fin.succ i)
  have hΔ_r_decreasing : ∀ j : Fin n_fine, Δ_r (Fin.succ j) ≤ Δ_r j.castSucc := by
    intro j
    have h : Δ (Fin.succ (Fin.succ j)) < Δ (Fin.succ j).castSucc := hcfg.hΔ_strict (Fin.succ j)
    simpa [Δ_r] using h.le
  have hΔ_r_j_le_Δ1 : ∀ j : Fin n_fine, Δ_r j.castSucc ≤ Δ 1 := by
    have h_helper : ∀ (p : ℕ) (h : p < n_fine + 1),
        Δ (Fin.succ (⟨p, h⟩ : Fin (n_fine + 1))) ≤ Δ 1 := by
      intro p h
      induction p with
      | zero =>
        have h_eq : Fin.succ (⟨0, h⟩ : Fin (n_fine + 1)) = (1 : Fin (n_fine + 2)) := by
          apply Fin.ext; simp
        rw [h_eq]
      | succ p ih =>
        have h' : p < n_fine + 1 := by omega
        have h_ih' := ih h'
        have h6 : Δ (Fin.succ (⟨p + 1, by omega⟩ : Fin (n_fine + 1))) <
                 Δ (⟨p + 1, by omega⟩ : Fin (n_fine + 1)).castSucc :=
          hcfg.hΔ_strict (⟨p + 1, by omega⟩ : Fin (n_fine + 1))
        have h7 : (⟨p + 1, by omega⟩ : Fin (n_fine + 1)).castSucc =
                   Fin.succ (⟨p, h'⟩ : Fin (n_fine + 1)) := by
          apply Fin.ext; simp
        rw [h7] at h6
        exact h6.le.trans h_ih'
    intro j
    have h2 : Δ_r j.castSucc = Δ (Fin.succ (j.castSucc : Fin (n_fine + 1))) := by
      simp [Δ_r]
    rw [h2]
    have h4 : j.val < n_fine + 1 := by
      have h5 : j.val < n_fine := Fin.is_lt j
      omega
    have h5 : (j.castSucc : Fin (n_fine + 1)) = ⟨j.val, h4⟩ := by
      apply Fin.ext; simp
    rw [h5]
    exact h_helper j.val h4

  have h_normal_r : ∀ (j : Fin n_fine), scaleClass_r j = ScaleClass.normal →
      IsSetBetweenScales config.pointSet (Δ_r (Fin.succ j)) (Δ_r j.castSucc) s (C_between_r j) := by
    intro j hj
    have h1 : scaleClass (Fin.succ j) = ScaleClass.normal := by
      simpa [scaleClass_r] using hj
    exact hcfg.h_normal (Fin.succ j) h1

  have h_good_r : ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass_r j = ScaleClass.good t_j →
      IsRegularBetweenScales config.pointSet (Δ_r (Fin.succ j)) (Δ_r j.castSucc) t_j
        (C_between_r j) (C_between_r j) := by
    intro j t_j hj
    have h1 : scaleClass (Fin.succ j) = ScaleClass.good t_j := by
      simpa [scaleClass_r] using hj
    exact hcfg.h_good (Fin.succ j) t_j h1

  let P_Q : Set Plane := homothetyS (Δ 1) Q.i Q.j ''
    (config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j)

  have h_between := between_scales_transfer_all (P := config.pointSet) (Δ₁ := Δ 1) (i₀ := Q.i) (j₀ := Q.j)
    (hcfg.hΔ_pos 1) (hcfg.hΔ_dyadic 1)
    n_fine Δ_r
    hΔ_r_dyadic hΔ_r_pos hΔ_r_decreasing hΔ_r_j_le_Δ1
    scaleClass_r
    s C_between_r
    h_normal_r h_good_r

  -- Fine point set equals P_Q
  have hfine_eq_P_Q : fineConfig.pointSet = P_Q := by
    have h' : ∀ (x : ℝ), BasicUniformization.dyadicSquare x Q.i Q.j =
        CombiningTheorem.dyadicSquare x Q.i Q.j := by intro x; rfl
    have h2 : (homothetyS (dyadicDelta m) Q.i Q.j ''
          (config.pointSet ∩ BasicUniformization.dyadicSquare (dyadicDelta m) Q.i Q.j)) =
        (homothetyS (Δ 1) Q.i Q.j ''
          (config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j)) := by
      rw [hΔ1_eq]
      <;> rw [h']
      <;> rfl
    rw [hfine_pointSet_eq, h2]
    <;> rfl

  -- h_normal
  have h_normal' : ∀ (j : Fin n_fine),
      scaleClass' j = ScaleClass.normal →
        IsSetBetweenScales fineConfig.pointSet
          (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_between' j) := by
    intro j hj
    have h1 : scaleClass_r j = ScaleClass.normal := by
      simpa [scaleClass_r, hscaleClass'_def] using hj
    have h2 : IsSetBetweenScales P_Q
        (Δ_r (Fin.succ j) / Δ 1) (Δ_r j.castSucc / Δ 1) s (C_between_r j) :=
      h_between.1 j h1
    rw [hfine_eq_P_Q]
    have h3 : Δ' (Fin.succ j) = Δ_r (Fin.succ j) / Δ 1 := by
      rw [hΔ'_def]
    have h4 : Δ' j.castSucc = Δ_r j.castSucc / Δ 1 := by
      rw [hΔ'_def]
    have h5 : C_between' j = C_between_r j := by
      simp [C_between_r, hC_between'_def]
    rw [h3, h4]
    have h6 : C_between_r j = C_between' j := h5.symm
    simpa [h6] using h2

  -- h_good
  have h_good' : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        IsRegularBetweenScales fineConfig.pointSet
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
          (C_between' j) (C_between' j) := by
    intro j t_j hj
    have h1 : scaleClass_r j = ScaleClass.good t_j := by
      simpa [scaleClass_r, hscaleClass'_def] using hj
    have h2 : IsRegularBetweenScales P_Q
        (Δ_r (Fin.succ j) / Δ 1) (Δ_r j.castSucc / Δ 1) t_j
        (C_between_r j) (C_between_r j) :=
      h_between.2 j t_j h1
    rw [hfine_eq_P_Q]
    have h3 : Δ' (Fin.succ j) = Δ_r (Fin.succ j) / Δ 1 := by
      rw [hΔ'_def]
    have h4 : Δ' j.castSucc = Δ_r j.castSucc / Δ 1 := by
      rw [hΔ'_def]
    have h5 : C_between' j = C_between_r j := by
      simp [C_between_r, hC_between'_def]
    rw [h3, h4]
    have h6 : C_between_r j = C_between' j := h5.symm
    simpa [h6] using h2

  -- C_between bounds via equation (89) logarithmic absorption
  have hδ_lt_one : dyadicDelta k < 1 := by
    have h2 : (1 : ℝ) < (2 : ℝ)^k := by
      have h21 : 1 < (2 : ℕ) := by norm_num
      have h22 := Nat.one_lt_pow (show k ≠ 0 from by omega) h21
      exact_mod_cast h22
    have h3 : dyadicDelta k = 1 / (2 : ℝ)^k := by
      simp [dyadicDelta] <;> ring
    rw [h3]
    apply (div_lt_one (by positivity)).mpr
    exact h2
  have hδbar_lt_one : dyadicDelta (k - m) < 1 := by
    have h_pos : 0 < k - m := by omega
    have h2 : (1 : ℝ) < (2 : ℝ)^(k - m) := by
      have h21 : 1 < (2 : ℕ) := by norm_num
      have h22 := Nat.one_lt_pow (show k - m ≠ 0 from by omega) h21
      exact_mod_cast h22
    have h3 : dyadicDelta (k - m) = 1 / (2 : ℝ)^(k - m) := by
      simp [dyadicDelta] <;> ring
    rw [h3]
    apply (div_lt_one (by positivity)).mpr
    exact h2
  have h_C_between_normal' : ∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
      C_between' j ≤ Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
        (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_N := by
    intro j hj
    set ratio : ℝ := Δ' j.castSucc / Δ' (Fin.succ j) with hratio_def
    have h_ratio_nonneg : 0 ≤ ratio := by
      apply div_nonneg <;> exact (hΔ'_pos _).le
    have h_coarse_scale : scaleClass (Fin.succ j) = ScaleClass.normal := by
      rw [←hscaleClass'_def j]; exact hj
    have h_coarse_bound : C_between (Fin.succ j) ≤
        Real.log (1 / dyadicDelta k) ^ C_P *
        (Δ (Fin.succ j).castSucc / Δ (Fin.succ (Fin.succ j))) ^ ε_N :=
      hcfg.h_C_between_normal (Fin.succ j) h_coarse_scale
    have h_ratio_eq : Δ (Fin.succ j).castSucc / Δ (Fin.succ (Fin.succ j)) = ratio := by
      simp only [hratio_def, hΔ'_def]
      have h_pos1 : 0 < Δ 1 := hcfg.hΔ_pos 1
      have h_fin_eq : (Fin.succ j).castSucc = Fin.succ j.castSucc := by
        apply Fin.ext <;> simp <;> omega
      rw [h_fin_eq]
      field_simp [h_pos1.ne']
    have h_coarse_bound' : C_between' j ≤
        Real.log (1 / dyadicDelta k) ^ C_P * ratio ^ ε_N := by
      have h1 : C_between' j = C_between (Fin.succ j) := by simp [hC_between'_def]
      rw [h1]; rw [h_ratio_eq] at h_coarse_bound; exact h_coarse_bound
    have h_main : C_between' j ≤
        Real.log (1 / dyadicDelta (k - m)) ^ (C_P + 2 * C_n) * ratio ^ ε_N :=
      equation89_cbetween_normal
        (hδ_pos := dyadicDelta_pos k) (hδ_lt_one := hδ_lt_one)
        (hδbar_pos := dyadicDelta_pos (k - m)) (hδbar_lt_one := hδbar_lt_one)
        (hτ_pos := hτ_pos) (hτ_lt_one := hτ_lt_one)
        (hCP := hCP) (hCn_ge1 := hCn_ge1)
        (hεN := hεN_pos) (h_ratio_nonneg := h_ratio_nonneg)
        (h_scale_sep := h_scale_sep) (h_small := h_small)
        (C_between := C_between' j) (h_coarse_bound := h_coarse_bound')
    rw [hCP_fine_eq]
    exact h_main

  have h_C_between_good' : ∀ (j : Fin n_fine) (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
      C_between' j ≤ Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
        (Δ' j.castSucc / Δ' (Fin.succ j)) ^ ε_G := by
    intro j t_j hj
    set ratio : ℝ := Δ' j.castSucc / Δ' (Fin.succ j) with hratio_def
    have h_ratio_nonneg : 0 ≤ ratio := by
      apply div_nonneg <;> exact (hΔ'_pos _).le
    have h_coarse_scale : scaleClass (Fin.succ j) = ScaleClass.good t_j := by
      rw [←hscaleClass'_def j]; exact hj
    have h_coarse_bound : C_between (Fin.succ j) ≤
        Real.log (1 / dyadicDelta k) ^ C_P *
        (Δ (Fin.succ j).castSucc / Δ (Fin.succ (Fin.succ j))) ^ ε_G :=
      hcfg.h_C_between_good (Fin.succ j) t_j h_coarse_scale
    have h_ratio_eq : Δ (Fin.succ j).castSucc / Δ (Fin.succ (Fin.succ j)) = ratio := by
      simp only [hratio_def, hΔ'_def]
      have h_pos1 : 0 < Δ 1 := hcfg.hΔ_pos 1
      have h_fin_eq : (Fin.succ j).castSucc = Fin.succ j.castSucc := by
        apply Fin.ext <;> simp <;> omega
      rw [h_fin_eq]
      field_simp [h_pos1.ne']
    have h_coarse_bound' : C_between' j ≤
        Real.log (1 / dyadicDelta k) ^ C_P * ratio ^ ε_G := by
      have h1 : C_between' j = C_between (Fin.succ j) := by simp [hC_between'_def]
      rw [h1]; rw [h_ratio_eq] at h_coarse_bound; exact h_coarse_bound
    have h_main : C_between' j ≤
        Real.log (1 / dyadicDelta (k - m)) ^ (C_P + 2 * C_n) * ratio ^ ε_G :=
      equation89_cbetween_good
        (hδ_pos := dyadicDelta_pos k) (hδ_lt_one := hδ_lt_one)
        (hδbar_pos := dyadicDelta_pos (k - m)) (hδbar_lt_one := hδbar_lt_one)
        (hτ_pos := hτ_pos) (hτ_lt_one := hτ_lt_one)
        (hCP := hCP) (hCn_ge1 := hCn_ge1)
        (hεG := hεG_pos) (h_ratio_nonneg := h_ratio_nonneg)
        (h_scale_sep := h_scale_sep) (h_small := h_small)
        (C_between := C_between' j) (h_coarse_bound := h_coarse_bound')
    rw [hCP_fine_eq]
    exact h_main

  -- Uniformity via dune's bridge + rangeUniformity_to_isUniformAtScales
  let a : Fin (n_fine + 1) → ℕ := fun i =>
    Classical.choose (hΔ'_dyadic i)
  have ha_spec1 : ∀ i, Δ' i ∈ dyadicScales := hΔ'_dyadic
  have ha_spec : ∀ i, Δ' i = dyadicDelta (a i) := by
    intro i
    dsimp only [a]
    have h := Classical.choose_spec (ha_spec1 i)
    simpa [dyadicDelta, zpow_neg] using h
  have ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j) := by
    intro j
    have h1 : Δ' (Fin.succ j) < Δ' j.castSucc := hΔ'_strict j
    rw [ha_spec (Fin.succ j), ha_spec j.castSucc] at h1
    have h2 : ¬ dyadicDelta (a j.castSucc) ≤ dyadicDelta (a (Fin.succ j)) := not_le.mpr h1
    have h3 : ¬ (a (Fin.succ j) ≤ a j.castSucc) := by
      rwa [dyadicDelta_le_iff] at h2
    omega
  have h_a_last : a (Fin.last n_fine) = k - m := by
    have h1 : Δ' (Fin.last n_fine) = dyadicDelta (a (Fin.last n_fine)) := ha_spec (Fin.last n_fine)
    have h2 : Δ' (Fin.last n_fine) = dyadicDelta (k - m) := hΔ'_end
    rw [h1] at h2
    have h3 : dyadicDelta (a (Fin.last n_fine)) = dyadicDelta (k - m) := h2
    have h4 : (2 : ℝ)^(a (Fin.last n_fine)) = (2 : ℝ)^(k - m) := by
      simpa [dyadicDelta] using h3
    have h4' : (2 : ℕ)^(a (Fin.last n_fine)) = (2 : ℕ)^(k - m) := by exact_mod_cast h4
    exact Nat.pow_right_injective (a := 2) (by norm_num) h4'
  have h_chain : ∀ (i : Fin (n_fine + 1)), Δ' (Fin.last n_fine) ≤ Δ' i := by
    have h_main : ∀ (k : ℕ), ∀ (i : Fin (n_fine + 1)), i.val + k = n_fine → Δ' (Fin.last n_fine) ≤ Δ' i := by
      intro k
      induction k with
      | zero =>
        intro i hi
        have h_val : i.val = n_fine := by omega
        have h_i_last : i = Fin.last n_fine := by
          apply Fin.ext
          simp [h_val, Fin.last]
        rw [h_i_last] <;> rfl
      | succ k ih =>
        intro i hi
        let i' : Fin (n_fine + 1) := ⟨i.val + 1, by omega⟩
        have h_i'_val : i'.val + k = n_fine := by
          simp [i', hi] <;> omega
        have h_ih' := ih i' h_i'_val
        let j : Fin n_fine := ⟨i.val, by omega⟩
        have h1 : j.castSucc = i := by apply Fin.ext <;> simp [j] <;> omega
        have h2 : Fin.succ j = i' := by apply Fin.ext <;> simp [j, i'] <;> omega
        have h_strict : Δ' i' < Δ' i := by
          have h := hΔ'_strict j
          rw [h2, h1] at h
          exact h
        exact h_ih'.trans h_strict.le
    intro i
    exact h_main (n_fine - i.val) i (by omega)
  have ha_last_max : ∀ i : Fin (n_fine + 1), a i ≤ a (Fin.last n_fine) := by
    intro i
    have h6 : Δ' (Fin.last n_fine) ≤ Δ' i := h_chain i
    have h4 : dyadicDelta (a (Fin.last n_fine)) ≤ dyadicDelta (a i) := by
      rw [←ha_spec (Fin.last n_fine), ←ha_spec i]
      exact h6
    exact dyadicDelta_le_iff.mp h4
  let S_full_norm : Finset (ℤ × ℤ) :=
    fineConfig.P₀.image (fun p : DyadicSquare (k - m) => (p.i, p.j))
  have hS_nonempty : S_full_norm.Nonempty := by
    rcases hP0_nonempty with ⟨p, hp⟩
    exact ⟨(p.i, p.j), Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have h_unit_S : ∀ idx ∈ S_full_norm,
      0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧ idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)) := by
    intro idx hidx
    rcases Finset.mem_image.mp hidx with ⟨p, hp, rfl⟩
    have h := h_squares_unit p hp
    rw [h_a_last]
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  have hP_Q_eq : homothetyS (Δ 1) Q.i Q.j ''
        (config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) =
      setFromIndices (dyadicDelta (a (Fin.last n_fine))) S_full_norm := by
    have h1 : fineConfig.pointSet =
        homothetyS (Δ 1) Q.i Q.j ''
          (config.pointSet ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j) := by
      exact hfine_eq_P_Q
    have h2 : fineConfig.pointSet = setFromIndices (dyadicDelta (k - m)) S_full_norm :=
      config_pointSet_eq_setFromIndices fineConfig
    rw [h_a_last] at *
    <;> exact h1.symm.trans h2
  have h_ha_spec_for_bridge : ∀ (i : Fin (n_fine + 1)),
      Δ (⟨i.val + 1, by omega⟩ : Fin (n_fine + 2)) / Δ 1 = dyadicDelta (a i) := by
    intro i
    have h_eq : (⟨i.val + 1, by omega⟩ : Fin (n_fine + 2)) = Fin.succ i := by
      apply Fin.ext; simp
    rw [h_eq, ←hΔ'_def i]
    exact ha_spec i
  have h_range : RangeUniformityProp n_fine a S_full_norm
      (fun j' : Fin n_fine => N ⟨j'.val + 1, by omega⟩) :=
    isUniformAtScales_to_rangeUniformity_Q
      (n := n_fine + 1) (n_fine := n_fine) (by omega)
      config.pointSet Δ N hcfg.h_uniform
      m Q hΔ1_eq hcfg.hΔ_end
      a h_ha_spec_for_bridge ha_mono ha_last_max
      S_full_norm hS_nonempty hP_Q_eq h_unit_S
  have hN'_eq : (fun j' : Fin n_fine => N ⟨j'.val + 1, by omega⟩) = N' := by
    funext j
    have h_eq : (⟨j.val + 1, by omega⟩ : Fin (n_fine + 1)) = Fin.succ j := by
      apply Fin.ext; simp
    rw [h_eq]
    exact (hN'_def j).symm
  rw [hN'_eq] at h_range
  have h_uniform' : IsUniformAtScales fineConfig.pointSet n_fine Δ' N' :=
    rangeUniformity_to_isUniformAtScales
      (h := h_range)
      (δ := dyadicDelta (k - m))
      (dyadicDelta_pos (k - m))
      (by rw [h_a_last])
      (hP_eq := by
        have h2 : fineConfig.pointSet = setFromIndices (dyadicDelta (k - m)) S_full_norm :=
          config_pointSet_eq_setFromIndices fineConfig
        exact h2)
      (hΔ'_dyadic := fun i => by
        have h : Δ' i = dyadicDelta (a i) := ha_spec i
        rw [h])
      ha_mono ha_last_max

  exact
    { hM_pos := hMQ_pos
    , hΔ_strict := hΔ'_strict
    , hΔ_end := hΔ'_end
    , hΔ_start := hΔ'_start
    , hΔ_pos := hΔ'_pos
    , hΔ_dyadic := hΔ'_dyadic
    , h_scale_ratio := h_scale_ratio'
    , h_uniform := h_uniform'
    , h_normal := h_normal'
    , h_good := h_good'
    , h_C_between_normal := h_C_between_normal'
    , h_C_between_good := h_C_between_good'
    }

/-- Construct fine `CombiningExtraHypotheses_v2` from coarse extra hypotheses.

    Slope bounds and improved incidence are supplied as parameters since they
    come from the B1 bridge construction and kestrel's tube adapter respectively.

    h_tj_ge_t, hε_inc_pos, and h_exp_condition are inherited/derived from the
    coarse extra hypotheses.

    NOTE: hP_set and hP_set_tj have been removed from CombiningExtraHypotheses_v2.
    At n=1, base cases derive global S-sets directly from CombiningConfig. -/
def fine_extra_from_coarse
    {n_fine : ℕ}
    {s t ε_G η lam ε_N C_P ε_inc : ℝ}
    {k m : ℕ}
    {M : ℕ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {Δ : Fin (n_fine + 2) → ℝ}
    {scaleClass : Fin (n_fine + 1) → ScaleClass}
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc
        (n_fine + 1) lam k M config Δ scaleClass)
    {MQ : ℕ}
    {lam_tail : ℝ}
    {fineConfig : CTNiceConfiguration (k - m) s (Real.rpow (dyadicDelta (k - m)) (-lam_tail)) MQ}
    (C_P_fine : ℝ)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (scaleClass' : Fin n_fine → ScaleClass)
    (hscaleClass'_def : ∀ j, scaleClass' j = scaleClass (Fin.succ j))
    -- Fine slope bound (from B1 bridge construction)
    (h_slope_fine : ∀ T ∈ fineConfig.T₀, |T.slope| ≤ 1) :
    CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc
        n_fine lam_tail (k - m) MQ fineConfig Δ' scaleClass' := by
  have h_tj_ge_t : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j → t ≤ t_j := by
    intro j t_j hj
    have h_coarse_scale : scaleClass (Fin.succ j) = ScaleClass.good t_j := by
      rw [←hscaleClass'_def j]; exact hj
    exact hextra.h_tj_ge_t (Fin.succ j) t_j h_coarse_scale
  have h_tj_le_two : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j → t_j ≤ 2 := by
    intro j t_j hj
    have h_coarse_scale : scaleClass (Fin.succ j) = ScaleClass.good t_j := by
      rw [←hscaleClass'_def j]; exact hj
    exact hextra.h_tj_le_two (Fin.succ j) t_j h_coarse_scale
  exact
    { h_slope := h_slope_fine
    , h_tj_ge_t := h_tj_ge_t
    , h_tj_le_two := h_tj_le_two
    , hε_inc_pos := hextra.hε_inc_pos
    , h_exp_condition := hextra.h_exp_condition
    }

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
