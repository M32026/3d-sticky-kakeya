import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreBroadness
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AngularStoppingHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.GlobalDirectionPacking
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.GCongr

/-!
# Capped max-score broadness witness (radius ≤ 1/2)

Variant of `max_score_broadness_tubes_with_witness` where the witness
radius is capped at 1/2. Maximality holds for r' ≤ 1/2.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section MaxScoreTubesWitnessHalf

variable {δ eta : ℝ}

/-- Max-score broadness witness capped at radius 1/2. -/
theorem max_score_broadness_tubes_with_witness_half
    (hδ : 0 < δ) (hδ_le_half : δ ≤ 1 / 2) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)}
    (hthrough : through.Nonempty) :
    ∃ (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ)),
      ‖w‖ = 1 ∧ δ ≤ r ∧ r ≤ 1 / 2 ∧
      W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r) ∧
      W.Nonempty ∧
      (∀ (v : Point3), ‖v‖ = 1 → ∀ s : ℝ, δ ≤ s → s ≤ r →
        ((W.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s).card : ℝ) ≤
          Real.rpow (s / r) eta * (W.card : ℝ)) ∧
      (∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 / 2 →
        ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
          Real.rpow (r' / r) eta * (W.card : ℝ)) := by
  let N := maxCapCount (through := through)
  let P (k : ℕ) : Set ℝ := {r | δ ≤ r ∧ r ≤ 1 / 2 ∧ N r ≥ k}
  have hP_closed : ∀ k, IsClosed (P k) := by
    intro k
    by_cases hk : k = 0
    · have h_set : P k = Set.Icc δ (1 / 2) := by
        ext r
        simp [P, hk] <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
      rw [h_set]; exact isClosed_Icc
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      have h_set_eq : P k =
          Set.Icc δ (1 / 2) ∩ ⋃ S ∈ through.powerset.filter (fun S => S.card ≥ k),
            {r : ℝ | Coverable S r} := by
        ext r
        simp only [P, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · intro h
          have h1 : N r ≥ k := h.2.2
          have h2 := (maxCapCount_ge_iff r hk_pos).mp h1
          rcases h2 with ⟨S, hS_powerset, hcard, hcover⟩
          have hS_filter : S ∈ through.powerset.filter (fun S => S.card ≥ k) := by
            simp only [Finset.mem_filter, hS_powerset, hcard, true_and]
          exact ⟨⟨h.1, h.2.1⟩, S, hS_filter, hcover⟩
        · rintro ⟨h_range, S, hS_filter, hcover⟩
          have hS_powerset : S ∈ through.powerset := (Finset.mem_filter.mp hS_filter).1
          have hcard : S.card ≥ k := (Finset.mem_filter.mp hS_filter).2
          have h3 : N r ≥ k :=
            (maxCapCount_ge_iff r hk_pos).mpr ⟨S, hS_powerset, hcard, hcover⟩
          exact ⟨h_range.1, h_range.2, h3⟩
      rw [h_set_eq]
      have h : IsClosed (⋃ S ∈ through.powerset.filter (fun S => S.card ≥ k), {r : ℝ | Coverable S r}) := by
        exact isClosed_biUnion_finset (fun S _ => isClosed_coverable S)
      exact IsClosed.inter isClosed_Icc h
  let a (k : ℕ) : ℝ := sInf (P k)
  let activeKs : Finset ℕ :=
    Finset.filter (fun k => (P k).Nonempty) (Finset.range (through.card + 1))
  let candidateRadii : Finset ℝ :=
    insert δ (insert (1 / 2) (Finset.image a activeKs))
  have h_candidate_nonempty : candidateRadii.Nonempty := by simp [candidateRadii]
  have h_candidates_in_range : ∀ r ∈ candidateRadii, δ ≤ r ∧ r ≤ 1 / 2 := by
    intro r hr
    have h_cases : r = δ ∨ r = (1 / 2 : ℝ) ∨ ∃ k ∈ activeKs, a k = r := by
      simp only [candidateRadii, Finset.mem_insert, Finset.mem_image] at hr <;> tauto
    rcases h_cases with (h_eq | h_eq | ⟨k, hk, h_eq⟩)
    · rw [h_eq]; exact ⟨by linarith, by linarith⟩
    · rw [h_eq]; exact ⟨hδ_le_half, by norm_num⟩
    · have hk_active : k ∈ activeKs := hk
      have hP_nonempty : (P k).Nonempty := (Finset.mem_filter.mp hk_active).2
      have h1δ : ∀ x ∈ P k, δ ≤ x := fun x hx => hx.1
      have h2 : δ ≤ a k := le_csInf hP_nonempty h1δ
      have h3 : a k ≤ 1 / 2 := by
        have h_closed2 : IsClosed (P k) := hP_closed k
        have h_bdd2 : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
        have h_ak_in : a k ∈ P k := h_closed2.csInf_mem hP_nonempty h_bdd2
        exact h_ak_in.2.1
      rw [←h_eq]; exact ⟨h2, h3⟩
  rcases Finset.exists_max_image candidateRadii
      (fun r : ℝ => (N r : ℝ) / Real.rpow r eta) h_candidate_nonempty with
    ⟨rStar, hrStar_in, hmax⟩
  have hrStar_range : δ ≤ rStar ∧ rStar ≤ 1 / 2 := h_candidates_in_range rStar hrStar_in
  have h_main_ineq : ∀ r : ℝ, δ ≤ r → r ≤ 1 / 2 →
      (N r : ℝ) / Real.rpow r eta ≤ (N rStar : ℝ) / Real.rpow rStar eta := by
    intro r hr1 hr2
    let k := N r
    have hk_in_range : k ∈ Finset.range (through.card + 1) := by
      simp [Finset.mem_range] <;> exact maxCapCount_le_card r
    have h_r_in_Pk : r ∈ P k := ⟨hr1, hr2, by simp [k]⟩
    have hP_k_nonempty : (P k).Nonempty := ⟨r, h_r_in_Pk⟩
    have hk_active : k ∈ activeKs := by
      simp only [activeKs, Finset.mem_filter, hk_in_range, hP_k_nonempty, true_and]
    have ha_k_in_Pk : a k ∈ P k := by
      have h_closed : IsClosed (P k) := hP_closed k
      have h_bdd : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
      exact h_closed.csInf_mem hP_k_nonempty h_bdd
    have h_bdd : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
    have ha_k_le_r : a k ≤ r := csInf_le h_bdd h_r_in_Pk
    have hN_ak : N (a k) = k := by
      have h1 : N (a k) ≥ k := ha_k_in_Pk.2.2
      have h2 : N (a k) ≤ N r := maxCapCount_mono (a k) r ha_k_le_r
      simpa [k] using h2.antisymm h1
    have h5 : 0 < a k := by have hδak : δ ≤ a k := ha_k_in_Pk.1; linarith [hδ]
    have h6 : 0 < r := by linarith [hδ]
    have h7 : Real.rpow (a k) eta ≤ Real.rpow r eta :=
      Real.rpow_le_rpow (by linarith) ha_k_le_r heta.le
    have h8 : (N r : ℝ) = (N (a k) : ℝ) := by simp [hN_ak, k]
    have h4 : (N r : ℝ) / Real.rpow r eta ≤ (N (a k) : ℝ) / Real.rpow (a k) eta := by
      rw [h8]
      have hA_nonneg : 0 ≤ (N (a k) : ℝ) := by positivity
      have hC_pos : 0 < Real.rpow (a k) eta := Real.rpow_pos_of_pos h5 _
      exact div_le_div_of_nonneg_left hA_nonneg hC_pos h7
    have h9 : a k ∈ candidateRadii := by
      simp only [candidateRadii, Finset.mem_insert, Finset.mem_image]
      exact Or.inr (Or.inr ⟨k, hk_active, rfl⟩)
    have h10 : (N (a k) : ℝ) / Real.rpow (a k) eta ≤
        (N rStar : ℝ) / Real.rpow rStar eta := hmax (a k) h9
    exact h4.trans h10
  have hN_rStar_le : N rStar ≤ through.card := maxCapCount_le_card rStar
  have hN_delta_pos : 0 < N δ := by
    rcases hthrough with ⟨T, hT⟩
    let S : Finset (Kakeya.DeltaTube δ) := {T}
    have hS_pow : S ∈ through.powerset := by simp [S, Finset.mem_powerset, hT]
    have hcover : Coverable S δ := by
      refine ⟨T.direction, T.direction_unit, ?_⟩
      intro U hU
      have hU_eq : U = T := by simpa [S, Finset.mem_singleton] using hU
      rw [hU_eq]
      have h_angle : hairbrushAcuteDirectionAngle T.direction T.direction = 0 := by
        have h_inner : inner ℝ T.direction T.direction = 1 := by
          have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
            simpa [inner_self_eq_norm_sq_to_K] using rfl
          rw [h, T.direction_unit] <;> norm_num
        rw [hairbrushAcuteDirectionAngle, h_inner]
        have h_arccos : Real.arccos 1 = 0 := Real.arccos_one
        rw [h_arccos]
        have h_pi_pos : 0 < Real.pi := Real.pi_pos
        exact min_eq_left (by linarith)
      linarith
    let f : Finset (Kakeya.DeltaTube δ) → ℕ := fun S => if Coverable S δ then S.card else 0
    have h' : f S ≤ through.powerset.sup f := Finset.le_sup hS_pow
    have h_fS : f S = 1 := by simp [f, hcover, S]
    rw [h_fS] at h'
    exact h'
  have hN_rStar_pos : 0 < N rStar := by
    have h1 : (N δ : ℝ) / Real.rpow δ eta ≤ (N rStar : ℝ) / Real.rpow rStar eta :=
      h_main_ineq δ (by linarith) (by linarith)
    have hδ_pos : 0 < Real.rpow δ eta := Real.rpow_pos_of_pos hδ _
    have h2 : (N δ : ℝ) > 0 := by exact_mod_cast hN_delta_pos
    have h3 : (N rStar : ℝ) > 0 := by
      by_contra h4
      have h5 : (N rStar : ℝ) = 0 := by linarith
      rw [h5] at h1
      have h6 : (N δ : ℝ) / Real.rpow δ eta ≤ 0 := by simpa using h1
      have h7 : 0 < (N δ : ℝ) / Real.rpow δ eta := by positivity
      linarith
    exact_mod_cast h3
  have h_exists_cover : ∃ (S : Finset (Kakeya.DeltaTube δ)),
      S ∈ through.powerset ∧ S.card = N rStar ∧ Coverable S rStar := by
    have h1 : N rStar ≥ N rStar := by rfl
    have h2 := (maxCapCount_ge_iff rStar hN_rStar_pos).mp h1
    rcases h2 with ⟨S, hS_powerset, hcard, hcover⟩
    let f : Finset (Kakeya.DeltaTube δ) → ℕ := fun S => if Coverable S rStar then S.card else 0
    have h3 : f S ≤ through.powerset.sup f := Finset.le_sup hS_powerset
    have h4 : f S = S.card := by simpa [f, hcover] using rfl
    rw [h4] at h3
    have h5 : S.card ≤ N rStar := h3
    have h6 : S.card = N rStar := by linarith
    exact ⟨S, hS_powerset, h6, hcover⟩
  rcases h_exists_cover with ⟨S, hS_powerset, hS_card, hcover⟩
  rcases hcover with ⟨w, hw_norm, hS_in_cap⟩
  let W : Finset (Kakeya.DeltaTube δ) :=
    through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ rStar)
  have hS_sub_W : S ⊆ W := by
    intro T hT
    have hT_in_through : T ∈ through := Finset.mem_powerset.mp hS_powerset hT
    have h_angle : hairbrushAcuteDirectionAngle T.direction w ≤ rStar := hS_in_cap T hT
    exact Finset.mem_filter.mpr ⟨hT_in_through, h_angle⟩
  have hW_ge_N : W.card ≥ N rStar := by
    have h1 : S.card ≤ W.card := Finset.card_le_card hS_sub_W
    rw [hS_card] at h1
    exact h1
  have hW_le_N : W.card ≤ N rStar := maxCapCount_ge_count rStar w hw_norm
  have hW_card : W.card = N rStar := by linarith
  have hW_nonempty : W.Nonempty := by
    have h1 : 0 < W.card := by rw [hW_card] <;> exact hN_rStar_pos
    exact Finset.card_pos.mp h1
  have hrStar_pos : 0 < rStar := by linarith [hrStar_range.1]
  have h_broad_W : ∀ (v : Point3), ‖v‖ = 1 → ∀ s : ℝ, δ ≤ s → s ≤ rStar →
      ((W.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s).card : ℝ) ≤
        Real.rpow (s / rStar) eta * (W.card : ℝ) := by
    intro v hv s hsδ hs
    have h1 : (W.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s) ⊆
        through.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s := by
      intro T hT
      have hT_in_W : T ∈ W := (Finset.mem_filter.mp hT).1
      have hT_in_through : T ∈ through := (Finset.mem_filter.mp hT_in_W).1
      have h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ s := (Finset.mem_filter.mp hT).2
      exact Finset.mem_filter.mpr ⟨hT_in_through, h_angle⟩
    have h2 : ((W.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s).card : ℝ) ≤
        (N s : ℝ) := by
      exact_mod_cast (Finset.card_le_card h1).trans (maxCapCount_ge_count s v hv)
    have h3 : δ ≤ s := hsδ
    have h4 : s ≤ 1 / 2 := hs.trans hrStar_range.2
    have h5 : (N s : ℝ) / Real.rpow s eta ≤ (N rStar : ℝ) / Real.rpow rStar eta :=
      h_main_ineq s h3 h4
    have h6 : 0 < s := by linarith [hδ]
    have h7 : 0 < Real.rpow s eta := Real.rpow_pos_of_pos h6 _
    have h8 : 0 < Real.rpow rStar eta := Real.rpow_pos_of_pos hrStar_pos _
    have h_div : Real.rpow (s / rStar) eta = Real.rpow s eta / Real.rpow rStar eta :=
      Real.div_rpow (by linarith) (by linarith) eta
    have h9 : (N s : ℝ) ≤ Real.rpow (s / rStar) eta * (N rStar : ℝ) := by
      rw [h_div]
      have h10 : (N s : ℝ) / Real.rpow s eta ≤ (N rStar : ℝ) / Real.rpow rStar eta := h5
      have h_goal : (N s : ℝ) ≤ (N rStar : ℝ) * (Real.rpow s eta / Real.rpow rStar eta) := by
        have h_eq1 : (N s : ℝ) = ((N s : ℝ) / Real.rpow s eta) * Real.rpow s eta := by
          field_simp [h7.ne'] <;> ring
        rw [h_eq1]
        have h_pos : 0 ≤ Real.rpow s eta := by positivity
        have h_mul : ((N s : ℝ) / Real.rpow s eta) * Real.rpow s eta ≤
            ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow s eta :=
          mul_le_mul_of_nonneg_right h10 h_pos
        have h_rhs : ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow s eta =
            (N rStar : ℝ) * (Real.rpow s eta / Real.rpow rStar eta) := by ring
        rw [h_rhs] at h_mul
        exact h_mul
      have h_final_goal : (N s : ℝ) ≤ (Real.rpow s eta / Real.rpow rStar eta) * (N rStar : ℝ) := by
        have h_comm : (N rStar : ℝ) * (Real.rpow s eta / Real.rpow rStar eta) =
            (Real.rpow s eta / Real.rpow rStar eta) * (N rStar : ℝ) := by ring
        rw [h_comm] at h_goal
        exact h_goal
      exact h_final_goal
    have h10 : (W.card : ℝ) = (N rStar : ℝ) := by exact_mod_cast hW_card
    have h9' : (N s : ℝ) ≤ Real.rpow (s / rStar) eta * (W.card : ℝ) := by
      rw [h10] at * <;> exact h9
    exact h2.trans h9'
  have h_maximality : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 / 2 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        Real.rpow (r' / rStar) eta * (W.card : ℝ) := by
    intro v' hv' r' hr'δ hr'_half
    have h1 : ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        (N r' : ℝ) := by
      exact_mod_cast maxCapCount_ge_count r' v' hv'
    have h2 : (N r' : ℝ) / Real.rpow r' eta ≤ (N rStar : ℝ) / Real.rpow rStar eta :=
      h_main_ineq r' hr'δ hr'_half
    have h3 : 0 < r' := by linarith [hδ]
    have h4 : 0 < Real.rpow r' eta := Real.rpow_pos_of_pos h3 _
    have h5 : 0 < Real.rpow rStar eta := Real.rpow_pos_of_pos hrStar_pos _
    have h_div : Real.rpow (r' / rStar) eta = Real.rpow r' eta / Real.rpow rStar eta :=
      Real.div_rpow (by linarith) (by linarith) eta
    have h6 : (N r' : ℝ) ≤ Real.rpow (r' / rStar) eta * (N rStar : ℝ) := by
      rw [h_div]
      have h7 : (N r' : ℝ) / Real.rpow r' eta ≤ (N rStar : ℝ) / Real.rpow rStar eta := h2
      have h_goal : (N r' : ℝ) ≤ (N rStar : ℝ) * (Real.rpow r' eta / Real.rpow rStar eta) := by
        have h_eq1 : (N r' : ℝ) = ((N r' : ℝ) / Real.rpow r' eta) * Real.rpow r' eta := by
          field_simp [h4.ne'] <;> ring
        rw [h_eq1]
        have h_pos : 0 ≤ Real.rpow r' eta := by positivity
        have h_mul : ((N r' : ℝ) / Real.rpow r' eta) * Real.rpow r' eta ≤
            ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow r' eta :=
          mul_le_mul_of_nonneg_right h7 h_pos
        have h_rhs : ((N rStar : ℝ) / Real.rpow rStar eta) * Real.rpow r' eta =
            (N rStar : ℝ) * (Real.rpow r' eta / Real.rpow rStar eta) := by ring
        rw [h_rhs] at h_mul
        exact h_mul
      have h_final_goal : (N r' : ℝ) ≤ (Real.rpow r' eta / Real.rpow rStar eta) * (N rStar : ℝ) := by
        have h_comm : (N rStar : ℝ) * (Real.rpow r' eta / Real.rpow rStar eta) =
            (Real.rpow r' eta / Real.rpow rStar eta) * (N rStar : ℝ) := by ring
        rw [h_comm] at h_goal
        exact h_goal
      exact h_final_goal
    have h7 : (W.card : ℝ) = (N rStar : ℝ) := by exact_mod_cast hW_card
    have h6' : (N r' : ℝ) ≤ Real.rpow (r' / rStar) eta * (W.card : ℝ) := by
      rw [h7] at * <;> exact h6
    exact h1.trans h6'
  exact ⟨w, rStar, W, hw_norm, hrStar_range.1, hrStar_range.2, rfl, hW_nonempty,
    h_broad_W, h_maximality⟩

/-- Cardinality lower bound for the capped witness.
    Cover tube directions by a maximal 1/2-separated net N; |N| ≤ 1000.
    Each cap of radius 1/2 has ≤ (1/(2r))^η * |W| tubes by maximality.
    Hence |W| ≥ (1/1000) * (2r)^η * |through| ≥ (1/1000) * r^η * |through|. -/
lemma witness_cardinality_bound_half
    (hδ : 0 < δ) (hδ_le_half : δ ≤ 1 / 2) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)} (hthrough : through.Nonempty)
    (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ))
    (hw_norm : ‖w‖ = 1) (hrδ : δ ≤ r) (hr_half : r ≤ 1 / 2)
    (hW_eq : W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r))
    (h_max : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 / 2 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        Real.rpow (r' / r) eta * (W.card : ℝ)) :
    (W.card : ℝ) ≥ (1 / 1000 : ℝ) * Real.rpow r eta * (through.card : ℝ) := by
  let dirSet : Finset Point3 := through.image (fun T => T.direction)
  have h_dirs_unit : ∀ v ∈ dirSet, ‖v‖ = 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, _, rfl⟩
    exact T.direction_unit
  rcases maximal_acute_separated_subset (show (0 : ℝ) < 1 / 2 by norm_num) h_dirs_unit with
    ⟨N, hN_sub, hN_sep, hN_cover⟩
  have hN_unit : ∀ v ∈ N, ‖v‖ = 1 := fun v hv => h_dirs_unit v (hN_sub hv)
  have hN_card : N.card ≤ 1000 := global_direction_packing (by norm_num) (by norm_num) hN_unit hN_sep
  let cap (n : Point3) : Finset (Kakeya.DeltaTube δ) :=
    through.filter (fun T => hairbrushAcuteDirectionAngle T.direction n ≤ 1 / 2)
  have h_cover : through ⊆ Finset.biUnion N cap := by
    intro T hT
    have h_dir_in : T.direction ∈ dirSet := Finset.mem_image.mpr ⟨T, hT, rfl⟩
    rcases hN_cover T.direction h_dir_in with ⟨n, hn_in, h_lt⟩
    have h_le : hairbrushAcuteDirectionAngle T.direction n ≤ 1 / 2 := by linarith
    have hT_in_cap : T ∈ cap n := by
      simp only [cap, Finset.mem_filter]
      exact ⟨hT, h_le⟩
    exact Finset.mem_biUnion.mpr ⟨n, hn_in, hT_in_cap⟩
  have h_card_cover : through.card ≤ (Finset.biUnion N cap).card := Finset.card_le_card h_cover
  have h_union_card : (Finset.biUnion N cap).card ≤ ∑ n ∈ N, (cap n).card :=
    Finset.card_biUnion_le
  have h_each : ∀ n ∈ N, ((cap n).card : ℝ) ≤ Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := by
    intro n hn
    have hn_unit : ‖n‖ = 1 := h_dirs_unit n (hN_sub hn)
    exact h_max n hn_unit (1 / 2 : ℝ) (by linarith) (by norm_num)
  have h_sum : (∑ n ∈ N, (cap n).card : ℝ) ≤
      (N.card : ℝ) * (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ)) := by
    have h_step1 : (∑ n ∈ N, (cap n).card : ℝ) ≤
        ∑ n ∈ N, (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ)) :=
      Finset.sum_le_sum h_each
    have h_step2 : (∑ n ∈ N, (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ))) =
        (N.card : ℝ) * (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ)) := by
      rw [Finset.sum_const] <;> ring
    exact h_step1.trans_eq h_step2
  have hr_pos : 0 < r := by linarith [hδ]
  have h_rpow_r_pos : 0 < Real.rpow r eta := Real.rpow_pos_of_pos hr_pos _
  have h_rpow_half_pos : 0 < Real.rpow (1 / 2 : ℝ) eta := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (through.card : ℝ) ≤
      (N.card : ℝ) * Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := by
    have h2 : (through.card : ℝ) ≤ ((Finset.biUnion N cap).card : ℝ) := by exact_mod_cast h_card_cover
    have h3 : ((Finset.biUnion N cap).card : ℝ) ≤ (∑ n ∈ N, (cap n).card : ℝ) := by
      exact_mod_cast h_union_card
    have h_sum' : (∑ n ∈ N, (cap n).card : ℝ) ≤
        (N.card : ℝ) * Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := by
      simpa [mul_assoc] using h_sum
    exact h2.trans (h3.trans h_sum')
  have h4 : (N.card : ℝ) ≤ (1000 : ℝ) := by exact_mod_cast hN_card
  have h5 : (through.card : ℝ) ≤
      (1000 : ℝ) * Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := by
    have h51 : (N.card : ℝ) ≤ (1000 : ℝ) := by exact_mod_cast hN_card
    have h_rpow_pos : 0 < Real.rpow ((1 / 2 : ℝ) / r) eta :=
      Real.rpow_pos_of_pos (by positivity) eta
    have h_pos : 0 ≤ Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) :=
      mul_nonneg h_rpow_pos.le (by positivity)
    calc (through.card : ℝ)
      ≤ (N.card : ℝ) * Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := h1
    _ = (N.card : ℝ) * (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ)) := by ring
    _ ≤ (1000 : ℝ) * (Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_right h51 h_pos
    _ = (1000 : ℝ) * Real.rpow ((1 / 2 : ℝ) / r) eta * (W.card : ℝ) := by ring
  have hr_pos' : 0 < 2 * r := by linarith
  have h_div : (1 / 2 : ℝ) / r = (2 * r)⁻¹ := by
    field_simp [hr_pos.ne'] <;> ring
  have h6 : Real.rpow ((1 / 2 : ℝ) / r) eta = (Real.rpow (2 * r) eta)⁻¹ := by
    rw [h_div]
    exact Real.inv_rpow (by linarith) eta
  rw [h6] at h5
  have h_rpow_2r_pos : 0 < Real.rpow (2 * r) eta := Real.rpow_pos_of_pos (by linarith) eta
  have h_main_ineq : (through.card : ℝ) * Real.rpow (2 * r) eta ≤ (1000 : ℝ) * (W.card : ℝ) := by
    have h9 : (through.card : ℝ) ≤ (1000 : ℝ) * (Real.rpow (2 * r) eta)⁻¹ * (W.card : ℝ) := h5
    have h10 : (through.card : ℝ) * Real.rpow (2 * r) eta ≤
        ((1000 : ℝ) * (Real.rpow (2 * r) eta)⁻¹ * (W.card : ℝ)) * Real.rpow (2 * r) eta := by
      exact mul_le_mul_of_nonneg_right h9 (by positivity)
    have h11 : ((1000 : ℝ) * (Real.rpow (2 * r) eta)⁻¹ * (W.card : ℝ)) * Real.rpow (2 * r) eta =
        (1000 : ℝ) * (W.card : ℝ) := by
      have h12 : (Real.rpow (2 * r) eta)⁻¹ * Real.rpow (2 * r) eta = 1 := by
        field_simp [h_rpow_2r_pos.ne']
      ring_nf at * <;> rw [h12] <;> ring
    rw [h11] at h10
    exact h10
  have h9 : (W.card : ℝ) ≥ (1 / 1000 : ℝ) * Real.rpow (2 * r) eta * (through.card : ℝ) := by
    have h10 : 0 < (1000 : ℝ) := by norm_num
    calc (W.card : ℝ)
      = (1 / 1000 : ℝ) * ((1000 : ℝ) * (W.card : ℝ)) := by field_simp <;> ring
    _ ≥ (1 / 1000 : ℝ) * ((through.card : ℝ) * Real.rpow (2 * r) eta) := by gcongr
    _ = (1 / 1000 : ℝ) * Real.rpow (2 * r) eta * (through.card : ℝ) := by ring
  have h10 : Real.rpow (2 * r) eta ≥ Real.rpow r eta := by
    have h11 : r ≤ 2 * r := by linarith
    exact Real.rpow_le_rpow (by linarith) h11 heta.le
  calc (W.card : ℝ)
    ≥ (1 / 1000 : ℝ) * Real.rpow (2 * r) eta * (through.card : ℝ) := h9
  _ ≥ (1 / 1000 : ℝ) * Real.rpow r eta * (through.card : ℝ) := by gcongr

/-- ENNReal version of the capped cardinality bound. -/
lemma witness_cardinality_bound_half_ENNReal
    (hδ : 0 < δ) (hδ_le_half : δ ≤ 1 / 2) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)} (hthrough : through.Nonempty)
    (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ))
    (hw_norm : ‖w‖ = 1) (hrδ : δ ≤ r) (hr_half : r ≤ 1 / 2)
    (hW_eq : W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r))
    (h_max : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 / 2 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        Real.rpow (r' / r) eta * (W.card : ℝ)) :
    (W.card : ENNReal) ≥ (1 / 1000 : ENNReal) * ENNReal.ofReal (Real.rpow r eta) * (through.card : ENNReal) := by
  have h_real := witness_cardinality_bound_half hδ hδ_le_half heta hthrough w r W hw_norm hrδ hr_half hW_eq h_max
  have hr_pos : 0 < r := by linarith [hδ]
  have h_rpow_pos : 0 < Real.rpow r eta := Real.rpow_pos_of_pos hr_pos eta
  have h_rpow_nonneg : 0 ≤ Real.rpow r eta := h_rpow_pos.le
  have h_W_nonneg : 0 ≤ (W.card : ℝ) := by positivity
  have h_through_nonneg : 0 ≤ (through.card : ℝ) := by positivity
  have h1 : (W.card : ENNReal) ≥
      ENNReal.ofReal ((1 / 1000 : ℝ) * Real.rpow r eta * (through.card : ℝ)) := by
    exact_mod_cast h_real
  have h2 : ENNReal.ofReal ((1 / 1000 : ℝ) * Real.rpow r eta * (through.card : ℝ)) =
      (1 / 1000 : ENNReal) * ENNReal.ofReal (Real.rpow r eta) * (through.card : ENNReal) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    <;> simp [ENNReal.ofReal_natCast]
    <;> ring
  rw [h2] at h1
  exact h1

end MaxScoreTubesWitnessHalf

end Kakeya.Assouad
