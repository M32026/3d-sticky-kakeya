import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreBroadness
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card

/-!
# Max-score broadness witness for tube families

Adapts `max_score_broadness_point3_with_witness` to `Finset (Kakeya.DeltaTube δ)`.
Given a finite family of tubes, find a unit center `w`, radius `r ∈ [δ,1]`, and
a retained subfamily `W` (all tubes whose direction lies within angle `r` of `w`)
such that:
- `W` is nonempty and has the max-score broadness property at scale `r`;
- every cap in the original family is bounded by the same score ratio.

Whiteprint node: MaxScoreTubesWitness under HairbrushLabeledAngularStopping.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

section MaxScoreTubesWitness

variable {δ eta : ℝ}

/-- Max-score broadness witness for tube direction sets. -/
theorem max_score_broadness_tubes_with_witness
    (hδ : 0 < δ) (hδ_le1 : δ ≤ 1) (heta : 0 < eta)
    {through : Finset (Kakeya.DeltaTube δ)}
    (hthrough : through.Nonempty) :
    ∃ (w : Point3) (r : ℝ) (W : Finset (Kakeya.DeltaTube δ)),
      ‖w‖ = 1 ∧ δ ≤ r ∧ r ≤ 1 ∧
      W = through.filter (fun T => hairbrushAcuteDirectionAngle T.direction w ≤ r) ∧
      W.Nonempty ∧
      (∀ (v : Point3), ‖v‖ = 1 → ∀ s : ℝ, δ ≤ s → s ≤ r →
        ((W.filter fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s).card : ℝ) ≤
        Real.rpow (s / r) eta * (W.card : ℝ)) ∧
      (∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 →
        ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        Real.rpow (r' / r) eta * (W.card : ℝ)) := by
  let N := maxCapCount (through := through)
  let P (k : ℕ) : Set ℝ := {r | δ ≤ r ∧ r ≤ 1 ∧ N r ≥ k}
  have hP_closed : ∀ k, IsClosed (P k) := isClosed_P
  let a (k : ℕ) : ℝ := sInf (P k)
  let activeKs : Finset ℕ :=
    Finset.filter (fun k => (P k).Nonempty) (Finset.range (through.card + 1))
  let candidateRadii : Finset ℝ :=
    insert δ (insert 1 (Finset.image a activeKs))
  have h_candidate_nonempty : candidateRadii.Nonempty := by simp [candidateRadii]
  have h_candidates_in_range : ∀ r ∈ candidateRadii, δ ≤ r ∧ r ≤ 1 := by
    intro r hr
    have h_cases : r = δ ∨ r = 1 ∨ ∃ k ∈ activeKs, a k = r := by
      simp only [candidateRadii, Finset.mem_insert, Finset.mem_image] at hr <;> tauto
    rcases h_cases with (h_eq | h_eq | ⟨k, hk, h_eq⟩)
    · rw [h_eq]; exact ⟨by linarith, hδ_le1⟩
    · rw [h_eq]; exact ⟨hδ_le1, by linarith⟩
    · have hk_active : k ∈ activeKs := hk
      have hP_nonempty : (P k).Nonempty := (Finset.mem_filter.mp hk_active).2
      have h1δ : ∀ x ∈ P k, δ ≤ x := fun x hx => hx.1
      have h2 : δ ≤ a k := le_csInf hP_nonempty h1δ
      have h3 : a k ≤ 1 := by
        have h_closed2 : IsClosed (P k) := hP_closed k
        have h_bdd2 : BddBelow (P k) := ⟨δ, fun y hy => hy.1⟩
        have h_ak_in : a k ∈ P k := h_closed2.csInf_mem hP_nonempty h_bdd2
        exact h_ak_in.2.1
      rw [←h_eq]; exact ⟨h2, h3⟩
  rcases Finset.exists_max_image candidateRadii
      (fun r : ℝ => (N r : ℝ) / Real.rpow r eta) h_candidate_nonempty with
    ⟨rStar, hrStar_in, hmax⟩
  have hrStar_range : δ ≤ rStar ∧ rStar ≤ 1 := h_candidates_in_range rStar hrStar_in
  have h_main_ineq : ∀ r : ℝ, δ ≤ r → r ≤ 1 →
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
    have h4 : s ≤ 1 := hs.trans hrStar_range.2
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
  have h_maximality : ∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 →
      ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
      Real.rpow (r' / rStar) eta * (W.card : ℝ) := by
    intro v' hv' r' hr'δ hr'1
    have h1 : ((through.filter fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r').card : ℝ) ≤
        (N r' : ℝ) := by
      exact_mod_cast maxCapCount_ge_count r' v' hv'
    have h2 : (N r' : ℝ) / Real.rpow r' eta ≤ (N rStar : ℝ) / Real.rpow rStar eta :=
      h_main_ineq r' hr'δ hr'1
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

end MaxScoreTubesWitness

end Kakeya.Assouad
