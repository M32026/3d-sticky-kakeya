import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

/-!
# Mass-weighted retention

Select a subfamily retaining a `δ^eps` fraction of the total mass
(sum of per-tube shaded volumes), while also retaining at least `δ^eps`
fraction of the tube count.

## Proof

Sort tubes by shaded volume (descending), take the top `k = ceil(δ^eps * n)`.
The top-k average volume ≥ overall average, so the selected mass ≥ (k/n) * total ≥ δ^eps * total.

The key lemma `separated_subset_mass_bound` proves the inequality for any
subset G where every element of G has weight ≥ every element outside G.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-! ### Helper: existence of a separated top-weight subset -/

/-- Given a finset `s` and weight function `w`, there exists a subset `G` of
cardinality `k` such that every element of `G` has weight ≥ every element of
`s \\ G`. This is the "top k by weight" subset. -/
lemma exists_separated_subset
    {α : Type*} [DecidableEq α] {s : Finset α} {w : α → ENNReal} {k : ℕ}
    (hk : k ≤ s.card) :
    ∃ (G : Finset α), G ⊆ s ∧ G.card = k ∧
      (∀ a ∈ G, ∀ b ∈ s \ G, w a ≥ w b) := by
  induction k with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    simp
  | succ k ih =>
    rcases ih (by omega) with ⟨Gk, hGk_sub, hGk_card, hGk_sep⟩
    have h_rem_card : (s \ Gk).card = s.card - k := by
      have h_disj : Disjoint (s \ Gk) Gk := Finset.disjoint_sdiff.symm
      have h_union : (s \ Gk) ∪ Gk = s := Finset.sdiff_union_of_subset hGk_sub
      have h : (s \ Gk).card + Gk.card = s.card := by
        rw [← Finset.card_union_of_disjoint h_disj, h_union]
      omega
    have h_rem_nonempty : (s \ Gk).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h] at h_rem_card
      simp at h_rem_card <;> omega
    rcases Finset.exists_max_image (s \ Gk) w h_rem_nonempty with ⟨a, ha_in, ha_max⟩
    let G := insert a Gk
    have h_a_notin_Gk : a ∉ Gk := (Finset.mem_sdiff.mp ha_in).2
    have hG_sub : G ⊆ s := by
      intro x hx
      simp only [G, Finset.mem_insert] at hx
      rcases hx with (rfl | hx)
      · exact (Finset.mem_sdiff.mp ha_in).1
      · exact hGk_sub hx
    have hG_card : G.card = k + 1 := by
      have h : (insert a Gk).card = Gk.card + 1 := by
        simp [h_a_notin_Gk] <;> omega
      have h' : (insert a Gk).card = k + 1 := by
        rw [h, hGk_card] <;> omega
      simpa [G] using h'
    have hG_sep : ∀ x ∈ G, ∀ y ∈ s \ G, w x ≥ w y := by
      intro x hx y hy
      by_cases h_x_eq_a : x = a
      · rw [h_x_eq_a]
        have h_y_in_s : y ∈ s := (Finset.mem_sdiff.mp hy).1
        have h_y_notin_G : y ∉ G := (Finset.mem_sdiff.mp hy).2
        have h_y_notin_Gk : y ∉ Gk := by
          intro h
          exact h_y_notin_G (Finset.mem_insert_of_mem h)
        have h_y_in_rem : y ∈ s \ Gk := Finset.mem_sdiff.mpr ⟨h_y_in_s, h_y_notin_Gk⟩
        exact ha_max y h_y_in_rem
      · have h_x_in_Gk : x ∈ Gk := by
          simp only [G, Finset.mem_insert] at hx
          tauto
        have h_y_in_s : y ∈ s := (Finset.mem_sdiff.mp hy).1
        have h_y_notin_G : y ∉ G := (Finset.mem_sdiff.mp hy).2
        have h_y_notin_Gk : y ∉ Gk := by
          intro h
          exact h_y_notin_G (Finset.mem_insert_of_mem h)
        have h_y_in_s_diff_Gk : y ∈ s \ Gk := Finset.mem_sdiff.mpr ⟨h_y_in_s, h_y_notin_Gk⟩
        exact hGk_sep x h_x_in_Gk y h_y_in_s_diff_Gk
    exact ⟨G, hG_sub, hG_card, hG_sep⟩

/-! ### Key inequality: separated subset has large mass -/

/-- If `G ⊆ s` and every element of `G` has weight ≥ every element of `s \\ G`,
then `|s| * sum(G) ≥ |G| * sum(s)`.

This is the "top k average ≥ overall average" inequality. -/
lemma separated_subset_mass_bound
    {α : Type*} [DecidableEq α] {s G : Finset α} {w : α → ENNReal}
    (hG_sub : G ⊆ s)
    (h_sep : ∀ a ∈ G, ∀ b ∈ s \ G, w a ≥ w b) :
    (s.card : ENNReal) * ∑ a ∈ G, w a ≥ (G.card : ENNReal) * ∑ a ∈ s, w a := by
  let H := s \ G
  have h_disj : Disjoint G H := Finset.disjoint_sdiff
  have h_union : G ∪ H = s := by
    rw [Finset.union_sdiff_of_subset hG_sub]
  have h_sum_H : ∀ a ∈ G, ∑ b ∈ H, w b ≤ (H.card : ENNReal) * w a := by
    intro a ha
    have h : ∀ b ∈ H, w b ≤ w a := by
      intro b hb
      exact h_sep a ha b hb
    calc ∑ b ∈ H, w b
      ≤ ∑ b ∈ H, w a := Finset.sum_le_sum h
    _ = (H.card : ENNReal) * w a := by
      simp [Finset.sum_const] <;> ring
  have h_main : (G.card : ENNReal) * ∑ b ∈ H, w b ≤
      (H.card : ENNReal) * ∑ a ∈ G, w a := by
    have h_eq1 : (G.card : ENNReal) * ∑ b ∈ H, w b =
        ∑ a ∈ G, (∑ b ∈ H, w b) := by
      have h : ∑ a ∈ G, (∑ b ∈ H, w b) = (G.card : ENNReal) * ∑ b ∈ H, w b := by
        rw [Finset.sum_const] <;> ring
      exact h.symm
    rw [h_eq1]
    have h_le : ∑ a ∈ G, (∑ b ∈ H, w b) ≤
        ∑ a ∈ G, ((H.card : ENNReal) * w a) :=
      Finset.sum_le_sum (fun a ha => h_sum_H a ha)
    have h_eq2 : ∑ a ∈ G, ((H.card : ENNReal) * w a) =
        (H.card : ENNReal) * ∑ a ∈ G, w a := by
      rw [Finset.mul_sum] <;> ring
    exact le_trans h_le h_eq2.le
  have h_total : ∑ a ∈ s, w a = (∑ a ∈ G, w a) + (∑ b ∈ H, w b) := by
    rw [← Finset.sum_union h_disj, h_union]
  rw [h_total]
  have h_card_nat : s.card = G.card + H.card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h_card : (s.card : ENNReal) = (G.card : ENNReal) + (H.card : ENNReal) := by
    rw [h_card_nat] <;> norm_cast
  rw [h_card]
  have h_rhs : ((G.card : ENNReal) + (H.card : ENNReal)) * ∑ a ∈ G, w a =
      (G.card : ENNReal) * ∑ a ∈ G, w a + (H.card : ENNReal) * ∑ a ∈ G, w a := by
    rw [add_mul]
  rw [h_rhs]
  have h_goal_rhs : (G.card : ENNReal) * ((∑ a ∈ G, w a) + (∑ b ∈ H, w b)) =
      (G.card : ENNReal) * ∑ a ∈ G, w a + (G.card : ENNReal) * ∑ b ∈ H, w b := by
    rw [mul_add]
  rw [h_goal_rhs]
  have h4 : (G.card : ENNReal) * ∑ a ∈ G, w a + (G.card : ENNReal) * ∑ b ∈ H, w b ≤
      (G.card : ENNReal) * ∑ a ∈ G, w a + (H.card : ENNReal) * ∑ a ∈ G, w a :=
    add_le_add_right h_main ((G.card : ENNReal) * ∑ a ∈ G, w a)
  exact h4

/-! ### Main mass-weighted retention lemma -/

/-- Select a subfamily `G` retaining at least `δ^eps` fraction of the mass
and at least `δ^eps` fraction of the tube count.

The shading `Y'` is the restriction of `Y` to `G`. -/
lemma mass_weighted_retention
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (eps : ℝ) (heps : 0 < eps) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (G : Kakeya.TubeFamily δ) (Y' : Kakeya.Shading G),
      G ⊆ F ∧
      (∀ T ∈ G, Y'.carrier T = Y.carrier T) ∧
      Kakeya.realRpowENN δ eps * Y.mass ≤ Y'.mass ∧
      (G.card : ENNReal) ≥ Kakeya.realRpowENN δ eps * (F.card : ENNReal) := by
  by_cases hF_empty : F = ∅
  · -- Empty family: trivial
    subst hF_empty
    let Y' : Kakeya.Shading (∅ : Kakeya.TubeFamily δ) :=
      { carrier := fun T => Y.carrier T
        measurable_carrier := fun T hT => by
          simpa using hT
        subset_tube := fun T hT => by
          simpa using hT }
    refine ⟨∅, Y', by simp, ?_⟩
    constructor
    · intro T hT
      simpa using hT
    · constructor
      · simp [Y', Kakeya.Shading.mass]
      · simp [Kakeya.Shading.mass]
  · -- Nonempty family
    have hF_nonempty : F.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hF_empty
    let n : ℕ := F.card
    have hn_pos : 0 < n := Finset.Nonempty.card_pos hF_nonempty
    let p : ℝ := Real.rpow δ eps
    have hp_nonneg : 0 ≤ p := Real.rpow_nonneg (by linarith) eps
    have hp_le_one : p ≤ 1 := by
      have h_eps_nonneg : 0 ≤ eps := by linarith
      have h : Real.rpow δ eps ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) h_eps_nonneg
      exact h
    let k : ℕ := Nat.ceil (p * (n : ℝ))
    have hk_le_n : k ≤ n := by
      have h1 : p * (n : ℝ) ≤ (n : ℝ) := by
        have h2 : p ≤ 1 := hp_le_one
        have h3 : p * (n : ℝ) ≤ 1 * (n : ℝ) := by gcongr <;> linarith
        linarith
      have h4 : k ≤ Nat.ceil (n : ℝ) := Nat.ceil_le_ceil h1
      simpa using h4
    have hk_ge : (k : ℝ) ≥ p * (n : ℝ) := Nat.le_ceil (p * (n : ℝ))
    let w : Kakeya.DeltaTube δ → ENNReal := fun T => volume (Y.carrier T)
    rcases exists_separated_subset (w := w) hk_le_n with ⟨G, hG_sub, hG_card, hG_sep⟩
    have h_mass_ineq : (F.card : ENNReal) * ∑ T ∈ G, w T ≥
        (G.card : ENNReal) * ∑ T ∈ F, w T :=
      separated_subset_mass_bound hG_sub hG_sep
    let Y' : Kakeya.Shading G :=
      { carrier := fun T => Y.carrier T
        measurable_carrier := fun T hT => Y.measurable_carrier (hG_sub hT)
        subset_tube := fun T hT => Y.subset_tube (hG_sub hT) }
    have hY'_mass : Y'.mass = ∑ T ∈ G, w T := by rfl
    have hF_mass : Y.mass = ∑ T ∈ F, w T := by rfl
    have hk_ennreal : (k : ENNReal) ≥ Kakeya.realRpowENN δ eps * (n : ENNReal) := by
      have h1 : (k : ℝ) ≥ p * (n : ℝ) := hk_ge
      have h2 : (k : ENNReal) ≥ ENNReal.ofReal (p * (n : ℝ)) := by
        exact_mod_cast h1
      have h3 : ENNReal.ofReal (p * (n : ℝ)) =
          ENNReal.ofReal p * (n : ENNReal) := by
        rw [ENNReal.ofReal_mul hp_nonneg] <;> norm_cast
      have h4 : ENNReal.ofReal p = Kakeya.realRpowENN δ eps := by
        rfl
      rw [h3, h4] at h2
      exact h2
    have hG_card_ennreal : (G.card : ENNReal) = (k : ENNReal) := by
      rw [hG_card] <;> norm_cast
    have h_main1 : (n : ENNReal) * Y'.mass ≥ (k : ENNReal) * Y.mass := by
      have hF_card_eq : (F.card : ENNReal) = (n : ENNReal) := by simp [n]
      have hG_card_eq2 : (G.card : ENNReal) = (k : ENNReal) := by
        rw [hG_card] <;> norm_cast
      have h : (n : ENNReal) * (∑ T ∈ G, w T) ≥ (k : ENNReal) * (∑ T ∈ F, w T) := by
        rw [← hF_card_eq, ← hG_card_eq2]
        exact h_mass_ineq
      simpa [hY'_mass, hF_mass] using h
    have h_main2 : (k : ENNReal) * Y.mass ≥
        Kakeya.realRpowENN δ eps * (n : ENNReal) * Y.mass := by
      have h : (k : ENNReal) ≥ Kakeya.realRpowENN δ eps * (n : ENNReal) := hk_ennreal
      exact mul_le_mul_of_nonneg_right h (by positivity)
    have h_n_pos_ennreal : (n : ENNReal) ≠ 0 := by
      exact_mod_cast hn_pos.ne'
    have h_n_top : (n : ENNReal) ≠ ⊤ := by
      simp
      <;> exact_mod_cast hn_pos.ne'
    have h_final_mass : Kakeya.realRpowENN δ eps * Y.mass ≤ Y'.mass := by
      have h : (n : ENNReal) * Y'.mass ≥
          (n : ENNReal) * (Kakeya.realRpowENN δ eps * Y.mass) := by
        calc (n : ENNReal) * Y'.mass
          ≥ (k : ENNReal) * Y.mass := h_main1
        _ ≥ Kakeya.realRpowENN δ eps * (n : ENNReal) * Y.mass := h_main2
        _ = (n : ENNReal) * (Kakeya.realRpowENN δ eps * Y.mass) := by ring
      have h_comm : Y'.mass * (n : ENNReal) ≥
          (Kakeya.realRpowENN δ eps * Y.mass) * (n : ENNReal) := by
        have h1 : (n : ENNReal) * Y'.mass = Y'.mass * (n : ENNReal) := by ring
        have h2 : (n : ENNReal) * (Kakeya.realRpowENN δ eps * Y.mass) =
            (Kakeya.realRpowENN δ eps * Y.mass) * (n : ENNReal) := by ring
        rw [h1, h2] at h
        exact h
      have h_iff : Y'.mass * (n : ENNReal) ≥
          (Kakeya.realRpowENN δ eps * Y.mass) * (n : ENNReal) ↔
          Y'.mass ≥ Kakeya.realRpowENN δ eps * Y.mass :=
        ENNReal.mul_le_mul_iff_left h_n_pos_ennreal h_n_top
      exact h_iff.mp h_comm
    have h_final_card : (G.card : ENNReal) ≥ Kakeya.realRpowENN δ eps * (F.card : ENNReal) := by
      have h1 : (F.card : ENNReal) = (n : ENNReal) := by rfl
      rw [h1, hG_card_ennreal]
      exact hk_ennreal
    have h_carrier_eq : ∀ T ∈ G, Y'.carrier T = Y.carrier T := by
      intro T _
      rfl
    exact ⟨G, Y', hG_sub, h_carrier_eq, h_final_mass, h_final_card⟩

end Kakeya.Assouad
