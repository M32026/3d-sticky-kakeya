import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements

/-!
# Angle separation lemmas for Wolff hairbrush preprocessing

Provides:
- `maximal_angle_separated_subset`: existence of a maximal angle-separated subfamily
- `angle_separated_cardinality`: cardinality bound from degree control
-/

noncomputable section

open Finset Set

namespace Kakeya.Assouad

/-- Symmetry of the acute angle between tube directions. -/
lemma hairbrushAcuteAngle_symm {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    hairbrushAcuteAngle T U = hairbrushAcuteAngle U T := by
  have h_inner : inner ℝ T.direction U.direction = inner ℝ U.direction T.direction :=
    real_inner_comm U.direction T.direction
  simp [hairbrushAcuteAngle, hairbrushAcuteDirectionAngle, h_inner]

/--
There exists a maximal angle-separated subfamily `F2` of `F`.

Maximality means every tube outside `F2` conflicts (intersects with acute angle
less than `δ`) with some tube inside `F2`.
-/
lemma maximal_angle_separated_subset
    {δ : ℝ} {F : Kakeya.TubeFamily δ} (hF_nonempty : F.Nonempty) :
    ∃ (F2 : Kakeya.TubeFamily δ),
      F2 ⊆ F ∧
      F2.Nonempty ∧
      HairbrushAngleSeparated F2 ∧
      ∀ T ∈ F, T ∉ F2 →
        ∃ U ∈ F2, T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ := by
  classical
  let candidates : Finset (Kakeya.TubeFamily δ) :=
    F.powerset.filter fun G => HairbrushAngleSeparated G
  have h_empty_in : (∅ : Kakeya.TubeFamily δ) ∈ candidates := by
    simp [candidates, HairbrushAngleSeparated]
  have h_nonempty : candidates.Nonempty := ⟨∅, h_empty_in⟩
  have h_exists : ∃ F2 ∈ candidates, ∀ G ∈ candidates, G.card ≤ F2.card :=
    Finset.exists_max_image candidates (fun G : Kakeya.TubeFamily δ => G.card) h_nonempty
  rcases h_exists with ⟨F2, hF2_in, hF2_max⟩
  have hF2_sub : F2 ⊆ F := by
    have h1 : F2 ∈ F.powerset := (Finset.mem_filter.mp hF2_in).1
    exact Finset.mem_powerset.mp h1
  have hF2_sep : HairbrushAngleSeparated F2 :=
    (Finset.mem_filter.mp hF2_in).2
  have hF2_nonempty : F2.Nonempty := by
    by_contra h
    have hF2_empty : F2 = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    rcases hF_nonempty with ⟨T, hT⟩
    let singleton : Kakeya.TubeFamily δ := {T}
    have h_singleton_sub : singleton ⊆ F := by
      simp [singleton, hT]
    have h_singleton_sep : HairbrushAngleSeparated singleton := by
      intro A hA B hB hne _
      simp [singleton] at hA hB
      have h_eq : A = B := by rw [hA, hB]
      exact False.elim (hne h_eq)
    have h_singleton_in : singleton ∈ candidates := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr h_singleton_sub, h_singleton_sep⟩
    have h_max2 : singleton.card ≤ F2.card := hF2_max singleton h_singleton_in
    rw [hF2_empty] at h_max2
    simp [singleton] at h_max2 <;> norm_num at h_max2
  refine' ⟨F2, hF2_sub, hF2_nonempty, hF2_sep, _⟩
  intro T0 hT0 hT0_notin
  by_contra h
  push Not at h
  let F2' := insert T0 F2
  have hF2'_sub : F2' ⊆ F := by
    intro x hx
    simp only [F2', Finset.mem_insert] at hx
    rcases hx with (rfl | hx2)
    · exact hT0
    · exact hF2_sub hx2
  have h_no_conflict : ∀ U ∈ F2,
      T0.carrier ∩ U.carrier ≠ ∅ → δ ≤ hairbrushAcuteAngle T0 U := by
    intro U hU hne
    have h' : (T0.carrier ∩ U.carrier).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    exact h U hU h'
  have hF2'_sep : HairbrushAngleSeparated F2' := by
    intro A hA B hB hne hAB
    have hA_cases : A = T0 ∨ A ∈ F2 := by
      simp only [F2', Finset.mem_insert] at hA <;> tauto
    have hB_cases : B = T0 ∨ B ∈ F2 := by
      simp only [F2', Finset.mem_insert] at hB <;> tauto
    rcases hA_cases with (hA_eq | hA2)
    · -- A = T0
      rcases hB_cases with (hB_eq | hB2)
      · -- B = T0
        have : A = B := by rw [hA_eq, hB_eq]
        contradiction
      · -- B ∈ F2
        have hAB' : T0.carrier ∩ B.carrier ≠ ∅ := by
          rw [hA_eq] at hAB
          exact hAB
        have h_result : δ ≤ hairbrushAcuteAngle T0 B := h_no_conflict B hB2 hAB'
        have h_goal : δ ≤ hairbrushAcuteAngle A B := by
          rw [hA_eq]
          exact h_result
        exact h_goal
    · -- A ∈ F2
      rcases hB_cases with (hB_eq | hB2)
      · -- B = T0
        have hAB' : T0.carrier ∩ A.carrier ≠ ∅ := by
          rw [hB_eq] at hAB
          rw [Set.inter_comm] <;> exact hAB
        have h_result : δ ≤ hairbrushAcuteAngle T0 A := h_no_conflict A hA2 hAB'
        have h_symm : hairbrushAcuteAngle T0 A = hairbrushAcuteAngle A T0 := hairbrushAcuteAngle_symm T0 A
        have h_goal : δ ≤ hairbrushAcuteAngle A B := by
          rw [hB_eq]
          rw [h_symm] at h_result
          exact h_result
        exact h_goal
      · exact hF2_sep A hA2 B hB2 hne hAB
  have hF2'_in : F2' ∈ candidates := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hF2'_sub, hF2'_sep⟩
  have h_card : F2'.card > F2.card := by
    have h : F2'.card = F2.card + 1 := by
      simp [F2', card_insert_of_notMem hT0_notin]
    linarith
  have h_contra := hF2_max F2' hF2'_in
  linarith

/--
Cardinality bound: if each tube has at most `D` conflicting tubes, then a
maximal angle-separated subfamily `F2` satisfies
`|F| ≤ (D + 1) * |F2|`.
-/
lemma angle_separated_cardinality
    {δ : ℝ} {F F2 : Kakeya.TubeFamily δ}
    (hF2_sub : F2 ⊆ F)
    (h_max : ∀ T ∈ F, T ∉ F2 →
      ∃ U ∈ F2, T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ)
    (D : ENNReal)
    (h_degree : ∀ T ∈ F,
      (↑(F.filter (fun U => T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ)).card : ENNReal) ≤ D) :
    F.enncard ≤ (D + 1) * F2.enncard := by
  classical
  let S := F \ F2
  have hS_sub : S ⊆ F := Finset.sdiff_subset (s := F) (t := F2)
  have h_disj : Disjoint F2 S := Finset.disjoint_sdiff
  have h_union : F2 ∪ S = F := Finset.union_sdiff_of_subset hF2_sub

  let g : Kakeya.DeltaTube δ → Kakeya.DeltaTube δ := fun T =>
    if hT : T ∈ S then
      Classical.choose (h_max T (hS_sub hT) (Finset.mem_sdiff.mp hT).2)
    else T

  have hg1 : ∀ T ∈ S, g T ∈ F2 := by
    intro T hT
    have hdef : g T = Classical.choose (h_max T (hS_sub hT) (Finset.mem_sdiff.mp hT).2) := by
      simp only [g, dif_pos hT]
    rw [hdef]
    exact (Classical.choose_spec (h_max T (hS_sub hT) (Finset.mem_sdiff.mp hT).2)).1

  have hg2 : ∀ T ∈ S,
      (g T).carrier ∩ T.carrier ≠ ∅ ∧ hairbrushAcuteAngle (g T) T < δ := by
    intro T hT
    set U : Kakeya.DeltaTube δ := Classical.choose (h_max T (hS_sub hT) (Finset.mem_sdiff.mp hT).2) with hU_def
    have hdef : g T = U := by
      simp only [g, dif_pos hT]
      <;> rfl
    have hspec : U ∈ F2 ∧ T.carrier ∩ U.carrier ≠ ∅ ∧ hairbrushAcuteAngle T U < δ :=
      Classical.choose_spec (h_max T (hS_sub hT) (Finset.mem_sdiff.mp hT).2)
    have h1 : U.carrier ∩ T.carrier ≠ ∅ := by
      rw [Set.inter_comm] <;> exact hspec.2.1
    have h2 : hairbrushAcuteAngle U T < δ := by
      have h3 : hairbrushAcuteAngle T U < δ := hspec.2.2
      rw [hairbrushAcuteAngle_symm T U] at h3
      exact h3
    rw [hdef]
    exact ⟨h1, h2⟩

  let preU (U : Kakeya.DeltaTube δ) : Finset (Kakeya.DeltaTube δ) :=
    S.filter (fun T => g T = U)

  have h_preU_sub : ∀ U ∈ F2, preU U ⊆
      F.filter (fun V => U.carrier ∩ V.carrier ≠ ∅ ∧ hairbrushAcuteAngle U V < δ) := by
    intro U hU T hT
    have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
    have hgT : g T = U := (Finset.mem_filter.mp hT).2
    have h_conf := hg2 T hT_in_S
    rw [hgT] at h_conf
    -- h_conf : U.carrier ∩ T.carrier ≠ ∅ ∧ hairbrushAcuteAngle U T < δ
    exact Finset.mem_filter.mpr ⟨hS_sub hT_in_S, h_conf⟩

  have h_preU_card : ∀ U ∈ F2, (↑(preU U).card : ENNReal) ≤ D := by
    intro U hU
    let conflictSet := F.filter (fun V => U.carrier ∩ V.carrier ≠ ∅ ∧ hairbrushAcuteAngle U V < δ)
    have h1 : preU U ⊆ conflictSet := h_preU_sub U hU
    have h2 : (↑(preU U).card : ENNReal) ≤ (↑conflictSet.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h1
    have h3 := h_degree U (hF2_sub hU)
    exact le_trans h2 h3

  have h_cover : S = Finset.biUnion F2 preU := by
    ext T
    simp only [Finset.mem_biUnion, preU, Finset.mem_filter]
    constructor
    · intro hT
      refine' ⟨g T, hg1 T hT, hT, rfl⟩
    · rintro ⟨U, hU, hT, _⟩
      exact hT

  have h_disj2 : ∀ U ∈ F2, ∀ V ∈ F2, U ≠ V → Disjoint (preU U) (preU V) := by
    intro U _ V _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h1 : g T = U := (Finset.mem_filter.mp hT1).2
    have h2 : g T = V := (Finset.mem_filter.mp hT2).2
    rw [h1] at h2
    exact hne h2

  have h_sum : (↑S.card : ENNReal) = ∑ U ∈ F2, (↑(preU U).card : ENNReal) := by
    have h : S.card = ∑ U ∈ F2, (preU U).card := by
      rw [h_cover, Finset.card_biUnion h_disj2]
    exact_mod_cast h

  calc
    F.enncard
      = (F2 ∪ S).enncard := by rw [h_union]
    _ = F2.enncard + (↑S.card : ENNReal) := by
      simp [Kakeya.TubeFamily.enncard, Finset.card_union_of_disjoint h_disj]
    _ = F2.enncard + ∑ U ∈ F2, (↑(preU U).card : ENNReal) := by rw [h_sum]
    _ ≤ F2.enncard + ∑ U ∈ F2, D := by
      gcongr with U hU
      exact h_preU_card U hU
    _ = F2.enncard + D * F2.enncard := by
      have h : ∑ U ∈ F2, D = D * (↑F2.card : ENNReal) := by
        simp [Finset.sum_const]
        <;> ring
      rw [h]
      <;> rfl
    _ = (D + 1) * F2.enncard := by
      rw [add_mul, one_mul]
      <;> ring

end Kakeya.Assouad
