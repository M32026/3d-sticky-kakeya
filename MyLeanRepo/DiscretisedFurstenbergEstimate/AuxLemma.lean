module

/-
  Auxiliary lemmas for HeavySquaresRedesign E-bound.

  1. Packing bounds: δ-separated finite sets have covering number ≥ |S|/C_pack.
  2. S-set → ball-growth: |S ∩ B(x,r)| ≤ C_pack * C * r^t * |S|.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace EnergyBoundLemmas

/-! ### Ball packing lemmas -/

/-- Helper: two points in the same third of [c-δ,c+δ] are at most 2δ/3 apart. -/
lemma region3_bound (δ c x y : ℝ) (hδ : 0 < δ)
    (hx1 : c - δ ≤ x) (hx2 : x ≤ c + δ) (hy1 : c - δ ≤ y) (hy2 : y ≤ c + δ)
    (hxr : (if x ≤ c - δ / 3 then (0 : Fin 3)
            else if x ≤ c + δ / 3 then 1 else 2) =
          (if y ≤ c - δ / 3 then (0 : Fin 3)
            else if y ≤ c + δ / 3 then 1 else 2)) :
    |x - y| ≤ 2 * δ / 3 := by
  by_cases h1 : x ≤ c - δ / 3
  · have h2 : y ≤ c - δ / 3 := by
      by_contra h3
      have h4 : (if y ≤ c - δ / 3 then (0 : Fin 3) else if y ≤ c + δ / 3 then 1 else 2) ≠ 0 := by
        rw [if_neg h3]
        split_ifs <;> simp <;> omega
      have h5 : (if x ≤ c - δ / 3 then (0 : Fin 3) else if x ≤ c + δ / 3 then 1 else 2) = 0 := by
        rw [if_pos h1]
      rw [h5] at hxr
      exact h4 hxr.symm
    rw [abs_le] <;> constructor <;> linarith
  · by_cases h2 : x ≤ c + δ / 3
    · have h3 : ¬(y ≤ c - δ / 3) := by
        intro h4
        have h5 : (if x ≤ c - δ / 3 then (0 : Fin 3) else if x ≤ c + δ / 3 then 1 else 2) = 1 := by
          rw [if_neg h1, if_pos h2]
        rw [h5] at hxr
        rw [if_pos h4] at hxr <;> simp at hxr <;> omega
      have h4 : y ≤ c + δ / 3 := by
        by_contra h5
        have h6 : (if x ≤ c - δ / 3 then (0 : Fin 3) else if x ≤ c + δ / 3 then 1 else 2) = 1 := by
          rw [if_neg h1, if_pos h2]
        rw [h6] at hxr
        rw [if_neg h3, if_neg h5] at hxr <;> simp at hxr <;> omega
      rw [abs_le] <;> constructor <;> linarith
    · have h_region_x : (if x ≤ c - δ / 3 then (0 : Fin 3) else if x ≤ c + δ / 3 then 1 else 2) = 2 := by
        rw [if_neg h1, if_neg h2]
      have h3 : c + δ / 3 < y := by
        by_cases h4 : y ≤ c + δ / 3
        · by_cases h5 : y ≤ c - δ / 3
          · have h6 : (if y ≤ c - δ / 3 then (0 : Fin 3) else if y ≤ c + δ / 3 then 1 else 2) = 0 := by
              rw [if_pos h5]
            have h7 : (2 : Fin 3) = 0 := by
              rw [h_region_x] at hxr
              rw [h6] at hxr
              exact hxr
            simp at h7
          · have h6 : (if y ≤ c - δ / 3 then (0 : Fin 3) else if y ≤ c + δ / 3 then 1 else 2) = 1 := by
              rw [if_neg h5, if_pos h4]
            have h7 : (2 : Fin 3) = 1 := by
              rw [h_region_x] at hxr
              rw [h6] at hxr
              exact hxr
            simp at h7
        · exact lt_of_not_ge h4
      rw [abs_le] <;> constructor <;> linarith

/-- A δ-ball in ℝ contains at most 3 δ-separated points. -/
lemma ball_3packing_real {δ : ℝ} (hδ : 0 < δ) {T : Finset ℝ}
    (hT_sep : SeparatedAt δ (T : Set ℝ)) {c : ℝ} :
    (T.filter (fun x => dist x c ≤ δ)).card ≤ 3 := by
  let B := T.filter (fun x => dist x c ≤ δ)
  have hB_sub : (B : Set ℝ) ⊆ (T : Set ℝ) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hB_sep : SeparatedAt δ (B : Set ℝ) := hT_sep.mono hB_sub
  let region : ℝ → Fin 3 := fun x =>
    if x ≤ c - δ / 3 then 0 else if x ≤ c + δ / 3 then 1 else 2
  have h_inj : Set.InjOn region (B : Set ℝ) := by
    intro x hx y hy hreg
    by_cases hneq : x ≠ y
    · have h_sep : δ ≤ dist x y := hB_sep hx hy hneq
      have hxc : |x - c| ≤ δ := by
        have h : dist x c ≤ δ := (Finset.mem_filter.mp hx).2
        simpa [dist_eq_norm, Real.norm_eq_abs] using h
      have hyc : |y - c| ≤ δ := by
        have h : dist y c ≤ δ := (Finset.mem_filter.mp hy).2
        simpa [dist_eq_norm, Real.norm_eq_abs] using h
      have hxc1 : c - δ ≤ x := by linarith [abs_le.mp hxc]
      have hxc2 : x ≤ c + δ := by linarith [abs_le.mp hxc]
      have hyc1 : c - δ ≤ y := by linarith [abs_le.mp hyc]
      have hyc2 : y ≤ c + δ := by linarith [abs_le.mp hyc]
      have h1 : |x - y| ≤ 2 * δ / 3 :=
        region3_bound δ c x y hδ hxc1 hxc2 hyc1 hyc2 hreg
      have h2 : dist x y = |x - y| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      rw [h2] at h_sep
      linarith
    · have h_eq : x = y := by tauto
      exact h_eq
  have h4 : B.card = (B.image region).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h5 : (B.image region).card ≤ 3 := by
    have h6 : B.image region ⊆ (Finset.univ : Finset (Fin 3)) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
      exact Finset.mem_univ _
    have h7 : (B.image region).card ≤ (Finset.univ : Finset (Fin 3)).card :=
      Finset.card_le_card h6
    simpa using h7
  rw [h4]
  exact h5

/-- A δ-ball in ℝ² (sup metric) contains at most 9 δ-separated points. -/
lemma ball_9packing_plane {δ : ℝ} (hδ : 0 < δ) {T : Finset (ℝ × ℝ)}
    (hT_sep : SeparatedAt δ (T : Set (ℝ × ℝ))) {c : ℝ × ℝ} :
    (T.filter (fun p => dist p c ≤ δ)).card ≤ 9 := by
  let B := T.filter (fun p => dist p c ≤ δ)
  have hB_sub : (B : Set (ℝ × ℝ)) ⊆ (T : Set (ℝ × ℝ)) := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hB_sep : SeparatedAt δ (B : Set (ℝ × ℝ)) := hT_sep.mono hB_sub
  let region : ℝ × ℝ → Fin 3 × Fin 3 := fun p =>
    let rx : Fin 3 :=
      if p.1 ≤ c.1 - δ / 3 then 0 else if p.1 ≤ c.1 + δ / 3 then 1 else 2
    let ry : Fin 3 :=
      if p.2 ≤ c.2 - δ / 3 then 0 else if p.2 ≤ c.2 + δ / 3 then 1 else 2
    (rx, ry)
  have h_inj : Set.InjOn region (B : Set (ℝ × ℝ)) := by
    intro p hp q hq hreg
    by_cases hneq : p ≠ q
    · have h_sep : δ ≤ dist p q := hB_sep hp hq hneq
      have hpc : dist p c ≤ δ := (Finset.mem_filter.mp hp).2
      have hqc : dist q c ≤ δ := (Finset.mem_filter.mp hq).2
      have hpc1 : c.1 - δ ≤ p.1 := by
        have h : max (dist p.1 c.1) (dist p.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hpc
        have h' : dist p.1 c.1 ≤ δ := (max_le_iff.mp h).1
        linarith [abs_le.mp h']
      have hpc2 : p.1 ≤ c.1 + δ := by
        have h : max (dist p.1 c.1) (dist p.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hpc
        have h' : dist p.1 c.1 ≤ δ := (max_le_iff.mp h).1
        linarith [abs_le.mp h']
      have hpc3 : c.2 - δ ≤ p.2 := by
        have h : max (dist p.1 c.1) (dist p.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hpc
        have h' : dist p.2 c.2 ≤ δ := (max_le_iff.mp h).2
        linarith [abs_le.mp h']
      have hpc4 : p.2 ≤ c.2 + δ := by
        have h : max (dist p.1 c.1) (dist p.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hpc
        have h' : dist p.2 c.2 ≤ δ := (max_le_iff.mp h).2
        linarith [abs_le.mp h']
      have hqc1 : c.1 - δ ≤ q.1 := by
        have h : max (dist q.1 c.1) (dist q.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hqc
        have h' : dist q.1 c.1 ≤ δ := (max_le_iff.mp h).1
        linarith [abs_le.mp h']
      have hqc2 : q.1 ≤ c.1 + δ := by
        have h : max (dist q.1 c.1) (dist q.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hqc
        have h' : dist q.1 c.1 ≤ δ := (max_le_iff.mp h).1
        linarith [abs_le.mp h']
      have hqc3 : c.2 - δ ≤ q.2 := by
        have h : max (dist q.1 c.1) (dist q.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hqc
        have h' : dist q.2 c.2 ≤ δ := (max_le_iff.mp h).2
        linarith [abs_le.mp h']
      have hqc4 : q.2 ≤ c.2 + δ := by
        have h : max (dist q.1 c.1) (dist q.2 c.2) ≤ δ := by simpa [Prod.dist_eq] using hqc
        have h' : dist q.2 c.2 ≤ δ := (max_le_iff.mp h).2
        linarith [abs_le.mp h']
      have hrx : (region p).1 = (region q).1 := by rw [hreg]
      have hry : (region p).2 = (region q).2 := by rw [hreg]
      have h1 : |p.1 - q.1| ≤ 2 * δ / 3 :=
        region3_bound δ c.1 p.1 q.1 hδ hpc1 hpc2 hqc1 hqc2 hrx
      have h2 : |p.2 - q.2| ≤ 2 * δ / 3 :=
        region3_bound δ c.2 p.2 q.2 hδ hpc3 hpc4 hqc3 hqc4 hry
      have h1' : dist p.1 q.1 ≤ 2 * δ / 3 := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using h1
      have h2' : dist p.2 q.2 ≤ 2 * δ / 3 := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using h2
      have h3 : dist p q ≤ 2 * δ / 3 := by
        simpa [Prod.dist_eq] using max_le h1' h2'
      linarith
    · have h_eq : p = q := by tauto
      exact h_eq
  have h4 : B.card = (B.image region).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h5 : (B.image region).card ≤ 9 := by
    have h6 : B.image region ⊆ (Finset.univ : Finset (Fin 3 × Fin 3)) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
      exact Finset.mem_univ _
    have h7 : (B.image region).card ≤ (Finset.univ : Finset (Fin 3 × Fin 3)).card :=
      Finset.card_le_card h6
    simpa using h7
  rw [h4]
  exact h5

/-! ### General packing-to-covering bound -/

/-- General packing bound: if every ε-ball contains at most C_pack points of S,
    then |S| ≤ C_pack * externalCoveringNumber(ε, S). -/
lemma packing_cover_bound {X : Type*} [MetricSpace X] [DecidableEq X]
    {ε : ℝ≥0} {S : Finset X}
    (hS_sep : SeparatedAt (ε : ℝ) (S : Set X)) (C_pack : ℕ) (hC_pack_pos : 0 < C_pack)
    (h_pack : ∀ (c : X), (S.filter (fun x => dist x c ≤ (ε : ℝ))).card ≤ C_pack) :
    (S.card : ENNReal) ≤ (C_pack : ENNReal) * (Metric.externalCoveringNumber ε (S : Set X) : ENNReal) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (C : Finset X),
    C.card = n ∧ Metric.IsCover ε (S : Set X) (C : Set X)
  have hP : ∃ n, P n := by
    refine ⟨S.card, S, rfl, ?_⟩
    intro x hx
    refine ⟨x, hx, ?_⟩
    simp
  let n₀ := Nat.find hP
  have hn₀ : P n₀ := Nat.find_spec hP
  rcases hn₀ with ⟨C₀, hC₀_card, hC₀_cover⟩
  have h1 : (n₀ : ℕ∞) ≤ Metric.externalCoveringNumber ε (S : Set X) := by
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    by_cases hC_fin : C.Finite
    · let C' := hC_fin.toFinset
      have hC'_eq : (C' : Set X) = C := hC_fin.coe_toFinset
      have hC'_cover : Metric.IsCover ε (S : Set X) (C' : Set X) := by
        rw [hC'_eq] <;> exact hC
      have h_ge : n₀ ≤ C'.card := by
        exact Nat.find_min' hP ⟨C', rfl, hC'_cover⟩
      have h_card : C.encard = (C'.card : ℕ∞) := by
        rw [← hC'_eq] <;> simp
      rw [h_card]
      exact_mod_cast h_ge
    · have h_top : C.encard = ⊤ := by simpa [Set.encard_eq_top_iff] using hC_fin
      rw [h_top] <;> simp
  have h2 : Metric.externalCoveringNumber ε (S : Set X) ≤ (C₀ : Set X).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hC₀_cover
  have hC0_encard : (C₀ : Set X).encard = (n₀ : ℕ∞) := by
    simp [hC₀_card]
  have h2' : Metric.externalCoveringNumber ε (S : Set X) ≤ (n₀ : ℕ∞) := by
    rw [hC0_encard] at h2
    exact h2
  have h3 : Metric.externalCoveringNumber ε (S : Set X) = (n₀ : ℕ∞) := by
    apply le_antisymm h2' h1
  have h4 : S.card ≤ C_pack * C₀.card := by
    have h_cover : ∀ x ∈ S, ∃ c ∈ C₀, dist x c ≤ (ε : ℝ) := by
      intro x hx
      have h := hC₀_cover hx
      rcases h with ⟨c, hc, hed⟩
      refine ⟨c, hc, ?_⟩
      have h10 : edist x c ≤ (ε : ENNReal) := by simpa using hed
      have h14 : dist x c ≤ (ε : ℝ) := by
        have h13 : edist x c = ENNReal.ofReal (dist x c) := by exact edist_dist x c
        have h15 : ENNReal.ofReal (dist x c) ≤ (ε : ENNReal) := by
          rw [←h13]; exact h10
        exact ENNReal.ofReal_le_coe.mp h15
      exact h14
    have h_sub : S ⊆ C₀.biUnion (fun c => S.filter (fun x => dist x c ≤ (ε : ℝ))) := by
      intro x hx
      rcases h_cover x hx with ⟨c, hc, hdist⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hx, hdist⟩⟩
    calc S.card
      ≤ (C₀.biUnion (fun c => S.filter (fun x => dist x c ≤ (ε : ℝ)))).card := Finset.card_le_card h_sub
    _ ≤ ∑ c ∈ C₀, (S.filter (fun x => dist x c ≤ (ε : ℝ))).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C₀, C_pack := by
      apply Finset.sum_le_sum; intro c _; exact h_pack c
    _ = C_pack * C₀.card := by simp [Finset.sum_const] <;> ring
  have h5 : (S.card : ENNReal) ≤ (C_pack : ENNReal) * (n₀ : ENNReal) := by
    rw [hC₀_card] at h4
    exact_mod_cast h4
  rw [h3]
  exact h5

/-! ### Covering number bounds -/

/-- For a δ-separated finite set in ℝ, covering_δ(S) ≥ |S| / 3. -/
lemma separated_covering_lower_real {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset ℝ} (hS_sep : SeparatedAt δ (S : Set ℝ)) :
    (S.card : ENNReal) ≤ 3 * Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ) := by
  have h1 : 0 ≤ δ := by linarith
  have hε : (δ.toNNReal : ℝ) = δ := by
    have h2 : (δ.toNNReal : ℝ) = max δ 0 := by simp
    rw [h2]
    exact max_eq_left h1
  have hS_sep' : SeparatedAt (δ.toNNReal : ℝ) (S : Set ℝ) := by
    rw [hε]; exact hS_sep
  have h_pack : ∀ (c : ℝ), (S.filter (fun x => dist x c ≤ (δ.toNNReal : ℝ))).card ≤ 3 := by
    intro c
    have h9 : (S.filter (fun x => dist x c ≤ (δ.toNNReal : ℝ))) =
        (S.filter (fun x => dist x c ≤ δ)) := by
      congr with x <;> rw [hε]
    rw [h9]
    exact ball_3packing_real hδ_pos hS_sep (c := c)
  have h_main := packing_cover_bound (ε := δ.toNNReal) hS_sep' 3 (by norm_num) h_pack
  exact h_main

/-- For any finite set, external covering number at scale δ is at most |S|. -/
lemma covering_upper_card {δ : ℝ} (hδ_pos : 0 < δ) {S : Finset ℝ} :
    Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ) ≤ (S.card : ENNReal) := by
  have h : Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ) ≤ (S : Set ℝ).encard :=
    Metric.externalCoveringNumber_le_encard_self (S : Set ℝ)
  have h2 : (S : Set ℝ).encard = (S.card : ℕ∞) := by simp
  rw [h2] at h
  exact_mod_cast h

/-- For a Δ-separated finite set in ℝ², covering_Δ(S) ≥ |S| / 9. -/
lemma separated_covering_lower_plane {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {S : Finset (ℝ × ℝ)} (hS_sep : SeparatedAt Δ (S : Set (ℝ × ℝ))) :
    (S.card : ENNReal) ≤ 9 * Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℝ × ℝ)) := by
  have h1 : 0 ≤ Δ := by linarith
  have hε : (Δ.toNNReal : ℝ) = Δ := by
    have h2 : (Δ.toNNReal : ℝ) = max Δ 0 := by simp
    rw [h2]
    exact max_eq_left h1
  have hS_sep' : SeparatedAt (Δ.toNNReal : ℝ) (S : Set (ℝ × ℝ)) := by
    rw [hε]; exact hS_sep
  have h_pack : ∀ (c : ℝ × ℝ), (S.filter (fun x => dist x c ≤ (Δ.toNNReal : ℝ))).card ≤ 9 := by
    intro c
    have h9 : (S.filter (fun x => dist x c ≤ (Δ.toNNReal : ℝ))) =
        (S.filter (fun x => dist x c ≤ Δ)) := by
      congr with x <;> rw [hε]
    rw [h9]
    exact ball_9packing_plane hΔ_pos hS_sep (c := c)
  have h_main := packing_cover_bound (ε := Δ.toNNReal) hS_sep' 9 (by norm_num) h_pack
  exact h_main

/-! ### S-set ball-growth bound -/

/-- |S ∩ B(x,r)| ≤ 9 * C * r^t * |S| for a (Δ,t,C)-set in ℝ², r ≥ Δ. -/
lemma sset_ball_card_bound_plane
    {Δ t C : ℝ} (hΔ_pos : 0 < Δ) (ht : 0 ≤ t) (hC_pos : 0 < C)
    {S : Finset (ℝ × ℝ)}
    (hS_sset : IsDeltaSSet Δ t C (S : Set (ℝ × ℝ)))
    (hS_sep : SeparatedAt Δ (S : Set (ℝ × ℝ)))
    {x : ℝ × ℝ} {r : ℝ} (hr : Δ ≤ r) :
    (S.filter (fun y => dist x y ≤ r)).card ≤
      (9 : ℝ) * C * r^t * (S.card : ℝ) := by
  let B := S.filter (fun y => dist x y ≤ r)
  have hB_in : (B : Set (ℝ × ℝ)) ⊆ (S : Set (ℝ × ℝ)) ∩ Metric.closedBall x r := by
    intro y hy
    have h1 : y ∈ S := (Finset.mem_filter.mp hy).1
    have h2 : dist x y ≤ r := (Finset.mem_filter.mp hy).2
    have h2' : dist y x ≤ r := by rw [dist_comm]; exact h2
    exact ⟨h1, by simpa [Metric.mem_closedBall] using h2'⟩
  have hB_sep : SeparatedAt Δ (B : Set (ℝ × ℝ)) :=
    hS_sep.mono (fun y hy => (Finset.mem_filter.mp hy).1)
  have h_mono : (Metric.externalCoveringNumber Δ.toNNReal (B : Set (ℝ × ℝ)) : ENNReal) ≤
      (Metric.externalCoveringNumber Δ.toNNReal ((S : Set (ℝ × ℝ)) ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hB_in
  have h_sset := hS_sset.2.2.2.2 x r hr
  have h_cover : (Metric.externalCoveringNumber Δ.toNNReal (B : Set (ℝ × ℝ)) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
        (Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℝ × ℝ))) :=
    h_mono.trans h_sset
  have h3 : (B.card : ENNReal) ≤
      9 * Metric.externalCoveringNumber Δ.toNNReal (B : Set (ℝ × ℝ)) :=
    separated_covering_lower_plane hΔ_pos hB_sep
  have h4 : (Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℝ × ℝ))) ≤ (S.card : ENNReal) := by
    have h : Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℝ × ℝ)) ≤ (S : Set (ℝ × ℝ)).encard :=
      Metric.externalCoveringNumber_le_encard_self (S : Set (ℝ × ℝ))
    have h2 : (S : Set (ℝ × ℝ)).encard = (S.card : ℕ∞) := by simp
    rw [h2] at h
    exact_mod_cast h
  have h5 : (B.card : ENNReal) ≤
      9 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (S.card : ENNReal)) := by
    calc (B.card : ENNReal)
      ≤ 9 * Metric.externalCoveringNumber Δ.toNNReal (B : Set (ℝ × ℝ)) := h3
    _ ≤ 9 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
              Metric.externalCoveringNumber Δ.toNNReal (S : Set (ℝ × ℝ))) := by gcongr
    _ ≤ 9 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (S.card : ENNReal)) := by gcongr
  have hr_nonneg : 0 ≤ r := by linarith
  have h_rpow_eq : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) :=
    ENNReal.ofReal_rpow_of_nonneg hr_nonneg ht
  let RHS := 9 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (S.card : ENNReal))
  have hfin_y : RHS ≠ ⊤ := by
    have hRHS_eq : RHS = 9 * (ENNReal.ofReal C * ENNReal.ofReal (r ^ t) * (S.card : ENNReal)) := by
      simp only [RHS]
      rw [h_rpow_eq] <;> rfl
    rw [hRHS_eq]
    simp [ENNReal.mul_ne_top, ENNReal.ofReal_ne_top]
    <;> tauto
  have h7 : (B.card : ENNReal).toReal ≤ RHS.toReal :=
    (ENNReal.toReal_le_toReal (by simp) hfin_y).mpr h5
  have h_rhs_real : RHS.toReal = 9 * C * r^t * (S.card : ℝ) := by
    have h_rpow_real : (ENNReal.ofReal r ^ t).toReal = r ^ t := by
      have h : (ENNReal.ofReal r ^ t).toReal = (ENNReal.ofReal r).toReal ^ t := by
        rw [← ENNReal.toReal_rpow]
      rw [h, ENNReal.toReal_ofReal hr_nonneg]
    simp [RHS, ENNReal.toReal_mul, h_rpow_real, ENNReal.toReal_ofReal,
      ENNReal.toReal_natCast, hC_pos.le, hr_nonneg, ht]
    <;> ring
  have h6 : (B.card : ℝ) ≤ RHS.toReal := by
    simpa [ENNReal.toReal_natCast] using h7
  rw [h_rhs_real] at h6
  exact h6

/-- |S ∩ I| ≤ 3 * C * r^s * |S| for a (δ,s,C)-set in ℝ and interval length r ≥ δ. -/
lemma sset_interval_card_bound
    {δ s C : ℝ} (hδ_pos : 0 < δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    {S : Finset ℝ}
    (hS_sset : IsDeltaSSet δ s C (S : Set ℝ))
    (hS_sep : SeparatedAt δ (S : Set ℝ))
    {a r : ℝ} (hr : δ ≤ r) :
    (S.filter (fun x => a ≤ x ∧ x ≤ a + r)).card ≤
      (3 : ℝ) * C * r^s * (S.card : ℝ) := by
  let I := Set.Icc a (a + r)
  let mid := a + r / 2
  have hI_sub_ball : I ⊆ Metric.closedBall mid r := by
    intro x hx
    have h_and : a ≤ x ∧ x ≤ a + r := by simpa [I, Set.mem_Icc] using hx
    have hxa : a ≤ x := h_and.1
    have hxb : x ≤ a + r := h_and.2
    have hmid : mid = a + r / 2 := by rfl
    have h_left : -r ≤ x - mid := by
      rw [hmid]; linarith
    have h_right : x - mid ≤ r := by
      rw [hmid]; linarith
    have h3 : |x - mid| ≤ r := by
      rw [abs_le]; exact ⟨h_left, h_right⟩
    have h4 : dist x mid ≤ r := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using h3
    simpa [Metric.mem_closedBall] using h4
  let B := S.filter (fun x => x ∈ I)
  have hB_in : (B : Set ℝ) ⊆ (S : Set ℝ) ∩ Metric.closedBall mid r := by
    intro y hy
    have h1 : y ∈ S := (Finset.mem_filter.mp hy).1
    have h2 : y ∈ I := (Finset.mem_filter.mp hy).2
    exact ⟨h1, hI_sub_ball h2⟩
  have hB_sep : SeparatedAt δ (B : Set ℝ) :=
    hS_sep.mono (fun y hy => (Finset.mem_filter.mp hy).1)
  have h_mono : (Metric.externalCoveringNumber δ.toNNReal (B : Set ℝ) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal ((S : Set ℝ) ∩ Metric.closedBall mid r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hB_in
  have h_sset := hS_sset.2.2.2.2 mid r hr
  have h_cover : (Metric.externalCoveringNumber δ.toNNReal (B : Set ℝ) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ)) :=
    h_mono.trans h_sset
  have h3 : (B.card : ENNReal) ≤
      3 * Metric.externalCoveringNumber δ.toNNReal (B : Set ℝ) :=
    separated_covering_lower_real hδ_pos hB_sep
  have h4 : (Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ)) ≤ (S.card : ENNReal) :=
    covering_upper_card hδ_pos
  have h5 : (B.card : ENNReal) ≤
      3 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (S.card : ENNReal)) := by
    calc (B.card : ENNReal)
      ≤ 3 * Metric.externalCoveringNumber δ.toNNReal (B : Set ℝ) := h3
    _ ≤ 3 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal (S : Set ℝ)) := by gcongr
    _ ≤ 3 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (S.card : ENNReal)) := by gcongr
  have hr_nonneg : 0 ≤ r := by linarith
  have h_rpow_eq : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
    ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs
  let RHS := 3 * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (S.card : ENNReal))
  have hfin_y : RHS ≠ ⊤ := by
    have hRHS_eq : RHS = 3 * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (S.card : ENNReal)) := by
      simp only [RHS]
      rw [h_rpow_eq] <;> rfl
    rw [hRHS_eq]
    simp [ENNReal.mul_ne_top, ENNReal.ofReal_ne_top]
    <;> tauto
  have h7 : (B.card : ENNReal).toReal ≤ RHS.toReal :=
    (ENNReal.toReal_le_toReal (by simp) hfin_y).mpr h5
  have h_rhs_real : RHS.toReal = 3 * C * r^s * (S.card : ℝ) := by
    have h_rpow_real : (ENNReal.ofReal r ^ s).toReal = r ^ s := by
      have h : (ENNReal.ofReal r ^ s).toReal = (ENNReal.ofReal r).toReal ^ s := by
        rw [← ENNReal.toReal_rpow]
      rw [h, ENNReal.toReal_ofReal hr_nonneg]
    simp [RHS, ENNReal.toReal_mul, h_rpow_real, ENNReal.toReal_ofReal,
      ENNReal.toReal_natCast, hC_pos.le, hr_nonneg, hs]
    <;> ring
  have h6 : (B.card : ℝ) ≤ RHS.toReal := by
    simpa [ENNReal.toReal_natCast] using h7
  rw [h_rhs_real] at h6
  exact h6

/-! ### Intersection bound via ball containment -/

/-- If `S1 ∩ S2` is contained in a closed ball of radius `r ≥ Δ`, and `S1` is a
    `(Δ,s,C)`-set that is `Δ`-separated, then
    `|S1 ∩ S2| ≤ 9 · C · r^s · |S1|`.

    This is the key intersection bound: tubes through two distant squares
    lie in a small ball in parameter space, and the S-set property controls
    how many can fit. -/
lemma intersection_bound_via_ball
    {Δ s C : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    {S1 S2 : Finset (ℝ × ℝ)}
    (hS1_sset : IsDeltaSSet Δ s C (S1 : Set (ℝ × ℝ)))
    (hS1_sep : SeparatedAt Δ (S1 : Set (ℝ × ℝ)))
    {center : ℝ × ℝ} {r : ℝ} (hr : Δ ≤ r)
    (h_geom : ∀ y ∈ S1 ∩ S2, dist y center ≤ r) :
    (S1 ∩ S2).card ≤ 9 * C * r^s * (S1.card : ℝ) := by
  have h1 : (S1 ∩ S2) ⊆ S1.filter (fun y => dist y center ≤ r) := by
    intro y hy
    have h2 : y ∈ S1 := (Finset.mem_inter.mp hy).1
    have h3 : dist y center ≤ r := h_geom y hy
    exact Finset.mem_filter.mpr ⟨h2, h3⟩
  have h4 : (S1 ∩ S2).card ≤ (S1.filter (fun y => dist y center ≤ r)).card :=
    Finset.card_le_card h1
  have h_filter_eq : S1.filter (fun y => dist y center ≤ r) =
      S1.filter (fun y => dist center y ≤ r) := by
    congr with y
    <;> rw [dist_comm]
  have h5 : (S1.filter (fun y => dist center y ≤ r)).card ≤
      9 * C * r^s * (S1.card : ℝ) :=
    sset_ball_card_bound_plane hΔ_pos hs hC_pos hS1_sset hS1_sep (x := center) (r := r) hr
  have h5' : (S1.filter (fun y => dist y center ≤ r)).card ≤
      9 * C * r^s * (S1.card : ℝ) := by
    rw [h_filter_eq] at *
    <;> exact h5
  have h4' : ((S1 ∩ S2).card : ℝ) ≤ ((S1.filter (fun y => dist y center ≤ r)).card : ℝ) := by
    exact_mod_cast h4
  have h5'' : ((S1.filter (fun y => dist y center ≤ r)).card : ℝ) ≤ 9 * C * r^s * (S1.card : ℝ) := by
    exact_mod_cast h5'
  exact le_trans h4' h5''

/-- Intersection bound with explicit distance factor.
    If `S1 ∩ S2` lies in a ball of radius `C_geom * Δ / d` (where `d ≥ Δ`),
    and `S1` is a `(Δ,s,C)`-set, then
    `|S1 ∩ S2| ≤ C_int · (Δ/d)^s · |S1|`
    with `C_int = 9 · C · C_geom^s`.

    The geometric hypothesis `h_geom` states that every element of `S1 ∩ S2`
    lies within distance `C_geom * Δ / d` of `center`. -/
lemma intersection_bound
    {Δ s C d : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hd_pos : 0 < d) (C_geom : ℝ) (hC_geom_pos : 0 < C_geom)
    {S1 S2 : Finset (ℝ × ℝ)}
    (hS1_sset : IsDeltaSSet Δ s C (S1 : Set (ℝ × ℝ)))
    (hS1_sep : SeparatedAt Δ (S1 : Set (ℝ × ℝ)))
    {center : ℝ × ℝ}
    (hr : Δ ≤ C_geom * Δ / d)
    (h_geom : ∀ y ∈ S1 ∩ S2, dist y center ≤ C_geom * Δ / d) :
    (S1 ∩ S2).card ≤ (9 * C * C_geom^s) * (Δ / d)^s * (S1.card : ℝ) := by
  have h_main := intersection_bound_via_ball hΔ_pos hs hC_pos hS1_sset hS1_sep hr h_geom
  have h41 : C_geom * Δ / d = C_geom * (Δ / d) := by ring
  have h42 : (C_geom * Δ / d)^s = (C_geom * (Δ / d))^s := by rw [h41]
  have h43 : (C_geom * (Δ / d))^s = C_geom^s * (Δ / d)^s := by
    have h5 : 0 ≤ C_geom := by linarith
    have h6 : 0 ≤ Δ / d := by positivity
    rw [Real.mul_rpow h5 h6] <;> ring
  have h44 : (C_geom * Δ / d)^s = C_geom^s * (Δ / d)^s := by
    rw [h42, h43]
  rw [h44] at h_main
  have h_final : (9 * C * (C_geom^s * (Δ / d)^s) * (S1.card : ℝ)) =
      (9 * C * C_geom^s) * (Δ / d)^s * (S1.card : ℝ) := by ring
  rw [h_final] at h_main
  exact h_main

/-- Intersection bound using direct cardinality growth (as in `IsFiniteDeltaSSet`).
    If `S1` satisfies `|S1 ∩ B(x,r)| ≤ C · r^s · |S1|` for all `r ≥ Δ`,
    and `S1 ∩ S2` lies in a ball of radius `r`, then
    `|S1 ∩ S2| ≤ C · r^s · |S1|`.

    This is the preferred version when `S1` comes from `IsFiniteDeltaSSet`,
    since it avoids the packing constant 9. -/
lemma intersection_bound_finite
    {Δ s C : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    {S1 S2 : Finset (ℝ × ℝ)}
    (h_growth : ∀ (x : ℝ × ℝ) (r : ℝ), Δ ≤ r →
      ((S1.filter fun y => dist y x ≤ r).card : ℝ) ≤ C * r ^ s * (S1.card : ℝ))
    {center : ℝ × ℝ} {r : ℝ} (hr : Δ ≤ r)
    (h_geom : ∀ y ∈ S1 ∩ S2, dist y center ≤ r) :
    (S1 ∩ S2).card ≤ C * r^s * (S1.card : ℝ) := by
  have h1 : (S1 ∩ S2) ⊆ S1.filter (fun y => dist y center ≤ r) := by
    intro y hy
    have h2 : y ∈ S1 := (Finset.mem_inter.mp hy).1
    have h3 : dist y center ≤ r := h_geom y hy
    exact Finset.mem_filter.mpr ⟨h2, h3⟩
  have h4 : (S1 ∩ S2).card ≤ (S1.filter (fun y => dist y center ≤ r)).card :=
    Finset.card_le_card h1
  have h5 : ((S1.filter (fun y => dist y center ≤ r)).card : ℝ) ≤ C * r^s * (S1.card : ℝ) :=
    h_growth center r hr
  have h4' : ((S1 ∩ S2).card : ℝ) ≤ ((S1.filter (fun y => dist y center ≤ r)).card : ℝ) := by
    exact_mod_cast h4
  exact le_trans h4' h5

/-- Distance-factor version using `IsFiniteDeltaSSet`-style growth bound.
    `|S1 ∩ S2| ≤ (C · C_geom^s) · (Δ/d)^s · |S1|`. -/
lemma intersection_bound_finite_dist
    {Δ s C d : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hd_pos : 0 < d) (C_geom : ℝ) (hC_geom_pos : 0 < C_geom)
    {S1 S2 : Finset (ℝ × ℝ)}
    (h_growth : ∀ (x : ℝ × ℝ) (r : ℝ), Δ ≤ r →
      ((S1.filter fun y => dist y x ≤ r).card : ℝ) ≤ C * r ^ s * (S1.card : ℝ))
    {center : ℝ × ℝ}
    (hr : Δ ≤ C_geom * Δ / d)
    (h_geom : ∀ y ∈ S1 ∩ S2, dist y center ≤ C_geom * Δ / d) :
    (S1 ∩ S2).card ≤ (C * C_geom^s) * (Δ / d)^s * (S1.card : ℝ) := by
  have h_main := intersection_bound_finite hΔ_pos hs hC_pos h_growth hr h_geom
  have h41 : C_geom * Δ / d = C_geom * (Δ / d) := by ring
  have h42 : (C_geom * Δ / d)^s = (C_geom * (Δ / d))^s := by rw [h41]
  have h43 : (C_geom * (Δ / d))^s = C_geom^s * (Δ / d)^s := by
    have h5 : 0 ≤ C_geom := by linarith
    have h6 : 0 ≤ Δ / d := by positivity
    rw [Real.mul_rpow h5 h6] <;> ring
  have h44 : (C_geom * Δ / d)^s = C_geom^s * (Δ / d)^s := by
    rw [h42, h43]
  rw [h44] at h_main
  have h_final : (C * (C_geom^s * (Δ / d)^s) * (S1.card : ℝ)) =
      (C * C_geom^s) * (Δ / d)^s * (S1.card : ℝ) := by ring
  rw [h_final] at h_main
  exact h_main

/-! ### Finite-growth interval bound (no packing constant) -/

/-- Interval bound for a finite set in ℝ with direct cardinality Frostman growth.
    If `|S ∩ B(x,r)| ≤ C·r^s·|S|` for all `r ≥ Δ`, then
    `|S ∩ [a, a+w]| ≤ C·w^s·|S|` for `w ≥ Δ`.

    Unlike `sset_interval_card_bound`, this uses the direct cardinality growth
    form (as in `IsFiniteDeltaSSet`) and has no packing constant 3. -/
lemma finite_growth_interval_bound
    {Δ s C : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    {S : Finset ℝ}
    (h_growth : ∀ (x : ℝ) (r : ℝ), Δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ C * r ^ s * (S.card : ℝ))
    {a w : ℝ} (hw : Δ ≤ w) :
    (S.filter (fun x => a ≤ x ∧ x ≤ a + w)).card ≤ C * w^s * (S.card : ℝ) := by
  let mid := a + w / 2
  have hmid : mid = a + w / 2 := by rfl
  have h1 : ∀ (x : ℝ), x ∈ S → (a ≤ x ∧ x ≤ a + w) → dist x mid ≤ w := by
    intro x _ hx
    have hxa : a ≤ x := hx.1
    have hxb : x ≤ a + w := hx.2
    have h_left : -w ≤ x - mid := by
      rw [hmid]; linarith
    have h_right : x - mid ≤ w := by
      rw [hmid]; linarith
    have h3 : |x - mid| ≤ w := by rw [abs_le]; exact ⟨h_left, h_right⟩
    simpa [dist_eq_norm, Real.norm_eq_abs] using h3
  have h2 : (S.filter (fun x => a ≤ x ∧ x ≤ a + w)) ⊆ S.filter (fun x => dist x mid ≤ w) := by
    intro x hx
    have h4 : x ∈ S := (Finset.mem_filter.mp hx).1
    have h5 : a ≤ x ∧ x ≤ a + w := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨h4, h1 x h4 h5⟩
  have h3 : (S.filter (fun x => a ≤ x ∧ x ≤ a + w)).card ≤
      (S.filter (fun x => dist x mid ≤ w)).card :=
    Finset.card_le_card h2
  have h4 : ((S.filter (fun x => dist x mid ≤ w)).card : ℝ) ≤ C * w^s * (S.card : ℝ) :=
    h_growth mid w hw
  have h5 : ((S.filter (fun x => a ≤ x ∧ x ≤ a + w)).card : ℝ) ≤ C * w^s * (S.card : ℝ) :=
    le_trans (by exact_mod_cast h3) h4
  exact_mod_cast h5

/-! ### Coarse-Lipschitz strip bound for 2D parameter sets -/

/-- If `S ⊆ ℝ²` is a `(Δ,s,C)`-set with `Δ`-separation, and satisfies the coarse
    Lipschitz property `|p.2 - q.2| ≤ M·|p.1 - q.1| + W` for all `p,q ∈ S`, then
    the number of points of `S` whose first coordinate lies in an interval of width
    `r ≥ max(Δ, W)` is bounded by `9 · C · ((M+2)·r)^s · |S|`.

    Geometric idea: within a vertical strip of width `r`, the coarse-Lipschitz
    property confines the second coordinate to an interval of width `M·r + W ≤ (M+1)·r`,
    so the entire intersection is contained in a ball of radius `(M+2)·r`.

    This is the key lemma for the intersection bound: tube parameters through a
    fixed square satisfy a coarse-Lipschitz property with `M = 1`, `W = O(Δ)`, so
    a slope interval of width `r` contains at most `O(C·r^s·|S|)` tubes. -/
lemma coarse_lipschitz_strip_bound
    {Δ s C M W r : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M) (hW_nonneg : 0 ≤ W) (hr_pos : 0 < r)
    (hW_le_r : W ≤ r) (hr_ge_delta : Δ ≤ r)
    {S : Finset (ℝ × ℝ)}
    (hS_sset : IsDeltaSSet Δ s C (S : Set (ℝ × ℝ)))
    (hS_sep : SeparatedAt Δ (S : Set (ℝ × ℝ)))
    (h_coarse : ∀ (p q : ℝ × ℝ), p ∈ S → q ∈ S → |p.2 - q.2| ≤ M * |p.1 - q.1| + W)
    {a : ℝ} :
    (S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + r)).card ≤
      (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) := by
  let A := S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + r)
  by_cases hA_empty : A = ∅
  · have h_goal : (A.card : ℝ) = 0 := by
      rw [hA_empty]; simp
    rw [h_goal]; positivity
  · have hA_nonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨p0, hp0_in_A⟩
    have hp0_in_S : p0 ∈ S := (Finset.mem_filter.mp hp0_in_A).1
    have h_ball : ∀ p ∈ A, dist p p0 ≤ (M + 2) * r := by
      intro p hp
      have hp_in_S : p ∈ S := (Finset.mem_filter.mp hp).1
      have hp_x1 : a ≤ p.1 := (Finset.mem_filter.mp hp).2.1
      have hp_x2 : p.1 ≤ a + r := (Finset.mem_filter.mp hp).2.2
      have hp0_x1 : a ≤ p0.1 := (Finset.mem_filter.mp hp0_in_A).2.1
      have hp0_x2 : p0.1 ≤ a + r := (Finset.mem_filter.mp hp0_in_A).2.2
      have hdx : |p.1 - p0.1| ≤ r := by
        rw [abs_le]; constructor <;> linarith
      have hdy : |p.2 - p0.2| ≤ M * |p.1 - p0.1| + W := h_coarse p p0 hp_in_S hp0_in_S
      have hdy' : |p.2 - p0.2| ≤ (M + 1) * r := by
        calc |p.2 - p0.2|
          ≤ M * |p.1 - p0.1| + W := hdy
        _ ≤ M * r + W := by gcongr
        _ ≤ M * r + r := by gcongr
        _ = (M + 1) * r := by ring
      have h1 : dist p.1 p0.1 = |p.1 - p0.1| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      have h2 : dist p.2 p0.2 = |p.2 - p0.2| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      have h_dist : dist p p0 = max (dist p.1 p0.1) (dist p.2 p0.2) := Prod.dist_eq
      have hdx' : |p.1 - p0.1| ≤ (M + 1) * r := by
        calc |p.1 - p0.1| ≤ r := hdx
          _ ≤ (M + 1) * r := by
            have h_pos2 : 0 ≤ r := by linarith
            nlinarith
      have h_max : max (|p.1 - p0.1|) (|p.2 - p0.2|) ≤ (M + 1) * r :=
        max_le hdx' hdy'
      have h_le : (M + 1) * r ≤ (M + 2) * r := by
        have h_pos2 : 0 ≤ r := by linarith
        nlinarith
      have h_ball_r : dist p p0 ≤ (M + 2) * r := by
        rw [h_dist, h1, h2]
        exact le_trans h_max h_le
      exact h_ball_r
    let B := S.filter (fun y => dist p0 y ≤ (M + 2) * r)
    have h1 : A ⊆ B := by
      intro p hp
      have h2 : p ∈ S := (Finset.mem_filter.mp hp).1
      have h3 : dist p p0 ≤ (M + 2) * r := h_ball p hp
      have h4 : dist p0 p ≤ (M + 2) * r := by rwa [dist_comm]
      exact Finset.mem_filter.mpr ⟨h2, h4⟩
    have h4 : A.card ≤ B.card := Finset.card_le_card h1
    have hR_ge_delta : Δ ≤ (M + 2) * r := by
      have h3 : r ≤ (M + 2) * r := by nlinarith
      linarith
    have h5 : B.card ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) :=
      sset_ball_card_bound_plane hΔ_pos hs hC_pos hS_sset hS_sep
        (x := p0) (r := (M + 2) * r) hR_ge_delta
    have h6 : (A.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr h4
    have h7 : (B.card : ℝ) ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) := by exact_mod_cast h5
    exact le_trans h6 h7

/-- Distance-factor version of `coarse_lipschitz_strip_bound`.
    If the slope interval has width `C_geom · Δ / d` (with `d ≥ Δ`), then
    `|points in strip| ≤ 9 · C · (M+2)^s · C_geom^s · (Δ/d)^s · |S|`. -/
lemma coarse_lipschitz_strip_bound_dist
    {Δ s C M W d : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M) (hW_nonneg : 0 ≤ W) (hd_pos : 0 < d)
    (C_geom : ℝ) (hC_geom_pos : 0 < C_geom)
    (hW_le_r : W ≤ C_geom * Δ / d) (hr_ge_delta : Δ ≤ C_geom * Δ / d)
    {S : Finset (ℝ × ℝ)}
    (hS_sset : IsDeltaSSet Δ s C (S : Set (ℝ × ℝ)))
    (hS_sep : SeparatedAt Δ (S : Set (ℝ × ℝ)))
    (h_coarse : ∀ (p q : ℝ × ℝ), p ∈ S → q ∈ S → |p.2 - q.2| ≤ M * |p.1 - q.1| + W)
    {a : ℝ} :
    (S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + C_geom * Δ / d)).card ≤
      (9 * C * (M + 2)^s * C_geom^s) * (Δ / d)^s * (S.card : ℝ) := by
  let r := C_geom * Δ / d
  have hr_pos : 0 < r := by positivity
  have h_main := coarse_lipschitz_strip_bound hΔ_pos hs hC_pos hM_nonneg hW_nonneg
    hr_pos hW_le_r hr_ge_delta hS_sset hS_sep h_coarse (a := a)
  have h41 : (M + 2) * r = (M + 2) * C_geom * (Δ / d) := by
    simp [r] <;> ring
  have h42 : ((M + 2) * r)^s = ((M + 2) * C_geom * (Δ / d))^s := by rw [h41]
  have h43 : ((M + 2) * C_geom * (Δ / d))^s = (M + 2)^s * C_geom^s * (Δ / d)^s := by
    have h5 : 0 ≤ M + 2 := by linarith
    have h6 : 0 ≤ C_geom := by linarith
    have h7 : 0 ≤ Δ / d := by positivity
    have h_step1 : (((M + 2) * C_geom) * (Δ / d))^s =
        ((M + 2) * C_geom)^s * (Δ / d)^s := Real.mul_rpow (by positivity) h7
    have h_step2 : ((M + 2) * C_geom)^s = (M + 2)^s * C_geom^s := Real.mul_rpow h5 h6
    rw [h_step1, h_step2] <;> ring
  rw [h42, h43] at h_main
  have h_final : (9 : ℝ) * C * ((M + 2)^s * C_geom^s * (Δ / d)^s) * (S.card : ℝ) =
      (9 * C * (M + 2)^s * C_geom^s) * (Δ / d)^s * (S.card : ℝ) := by ring
  rw [h_final] at h_main
  exact h_main

/-- Strip bound using direct cardinality Frostman growth (no packing constant 9).
    If `S` satisfies `|S ∩ B(x,r)| ≤ C·r^s·|S|` directly and has the coarse-Lipschitz
    property, then the vertical-strip bound is `C · ((M+2)·r)^s · |S|`. -/
lemma coarse_lipschitz_strip_bound_finite
    {Δ s C M W r : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M) (hW_nonneg : 0 ≤ W) (hr_pos : 0 < r)
    (hW_le_r : W ≤ r) (hr_ge_delta : Δ ≤ r)
    {S : Finset (ℝ × ℝ)}
    (h_growth : ∀ (x : ℝ × ℝ) (r : ℝ), Δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ C * r ^ s * (S.card : ℝ))
    (h_coarse : ∀ (p q : ℝ × ℝ), p ∈ S → q ∈ S → |p.2 - q.2| ≤ M * |p.1 - q.1| + W)
    {a : ℝ} :
    (S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + r)).card ≤
      C * ((M + 2) * r)^s * (S.card : ℝ) := by
  let A := S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + r)
  by_cases hA_empty : A = ∅
  · have h_goal : (A.card : ℝ) = 0 := by
      rw [hA_empty]; simp
    rw [h_goal]; positivity
  · have hA_nonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
    rcases hA_nonempty with ⟨p0, hp0_in_A⟩
    have hp0_in_S : p0 ∈ S := (Finset.mem_filter.mp hp0_in_A).1
    have h_ball : ∀ p ∈ A, dist p p0 ≤ (M + 2) * r := by
      intro p hp
      have hp_in_S : p ∈ S := (Finset.mem_filter.mp hp).1
      have hp_x1 : a ≤ p.1 := (Finset.mem_filter.mp hp).2.1
      have hp_x2 : p.1 ≤ a + r := (Finset.mem_filter.mp hp).2.2
      have hp0_x1 : a ≤ p0.1 := (Finset.mem_filter.mp hp0_in_A).2.1
      have hp0_x2 : p0.1 ≤ a + r := (Finset.mem_filter.mp hp0_in_A).2.2
      have hdx : |p.1 - p0.1| ≤ r := by
        rw [abs_le]; constructor <;> linarith
      have hdy : |p.2 - p0.2| ≤ M * |p.1 - p0.1| + W := h_coarse p p0 hp_in_S hp0_in_S
      have hdy' : |p.2 - p0.2| ≤ (M + 1) * r := by
        calc |p.2 - p0.2|
          ≤ M * |p.1 - p0.1| + W := hdy
        _ ≤ M * r + W := by gcongr
        _ ≤ M * r + r := by gcongr
        _ = (M + 1) * r := by ring
      have h1 : dist p.1 p0.1 = |p.1 - p0.1| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      have h2 : dist p.2 p0.2 = |p.2 - p0.2| := by
        simp [dist_eq_norm, Real.norm_eq_abs]
      have h_dist : dist p p0 = max (dist p.1 p0.1) (dist p.2 p0.2) := Prod.dist_eq
      have hdx' : |p.1 - p0.1| ≤ (M + 1) * r := by
        calc |p.1 - p0.1| ≤ r := hdx
          _ ≤ (M + 1) * r := by
            have h_pos2 : 0 ≤ r := by linarith
            nlinarith
      have h_max : max (|p.1 - p0.1|) (|p.2 - p0.2|) ≤ (M + 1) * r :=
        max_le hdx' hdy'
      have h_le : (M + 1) * r ≤ (M + 2) * r := by
        have h_pos2 : 0 ≤ r := by linarith
        nlinarith
      have h_ball_r : dist p p0 ≤ (M + 2) * r := by
        rw [h_dist, h1, h2]
        exact le_trans h_max h_le
      exact h_ball_r
    let B := S.filter (fun y => dist y p0 ≤ (M + 2) * r)
    have h1 : A ⊆ B := by
      intro p hp
      have h2 : p ∈ S := (Finset.mem_filter.mp hp).1
      have h3 : dist p p0 ≤ (M + 2) * r := h_ball p hp
      exact Finset.mem_filter.mpr ⟨h2, h3⟩
    have h4 : A.card ≤ B.card := Finset.card_le_card h1
    have hR_ge_delta : Δ ≤ (M + 2) * r := by
      have h3 : r ≤ (M + 2) * r := by nlinarith
      linarith
    have h5 : (B.card : ℝ) ≤ C * ((M + 2) * r)^s * (S.card : ℝ) :=
      h_growth p0 ((M + 2) * r) hR_ge_delta
    have h6 : (A.card : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr h4
    exact le_trans h6 h5

/-! ### Projection image S-set transfer -/

/-- If `S ⊆ ℝ²` is a `(Δ,s,C)`-set with separation, satisfies the coarse-Lipschitz
    property, and the first-coordinate projection is `≤K`-to-1, then the projection
    image `S' = {p.1 : p ∈ S}` satisfies the cardinality Frostman growth bound:

    `|S' ∩ [a, a+r]| ≤ 9 · K · C · ((M+2)·r)^s · |S'|`

    This is the key projection transfer lemma: the slope set of a tube family
    inherits the S-set property (in cardinality Frostman form) from the parameter
    set, using the coarse-Lipschitz geometry of tubes through a fixed square.

    The `≤K`-to-1 hypothesis is needed to relate `|S|` to `|S'|`. -/
lemma projection_image_growth_bound
    {Δ s C M W r K : ℝ} (hΔ_pos : 0 < Δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hM_nonneg : 0 ≤ M) (hW_nonneg : 0 ≤ W) (hr_pos : 0 < r)
    (hW_le_r : W ≤ r) (hr_ge_delta : Δ ≤ r)
    (hK_pos : 0 < K)
    {S : Finset (ℝ × ℝ)}
    (hS_sset : IsDeltaSSet Δ s C (S : Set (ℝ × ℝ)))
    (hS_sep : SeparatedAt Δ (S : Set (ℝ × ℝ)))
    (h_coarse : ∀ (p q : ℝ × ℝ), p ∈ S → q ∈ S → |p.2 - q.2| ≤ M * |p.1 - q.1| + W)
    (hK_to_one : ∀ (x : ℝ), (S.filter (fun p => p.1 = x)).card ≤ K)
    {a : ℝ} :
    let S' := S.image (fun p : ℝ × ℝ => p.1)
    (S'.filter (fun x => a ≤ x ∧ x ≤ a + r)).card ≤
      (9 : ℝ) * K * C * ((M + 2) * r)^s * (S'.card : ℝ) := by
  let S' := S.image (fun p : ℝ × ℝ => p.1)
  let A := S.filter (fun p => a ≤ p.1 ∧ p.1 ≤ a + r)
  let I_set := S'.filter (fun x => a ≤ x ∧ x ≤ a + r)
  -- Step 1: |I_set| ≤ |A| (image of preimage)
  have h1 : I_set.card ≤ A.card := by
    have h_img : I_set = A.image (fun p : ℝ × ℝ => p.1) := by
      ext x
      simp only [I_set, A, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hx_in_S', h_interval⟩
        rcases Finset.mem_image.mp hx_in_S' with ⟨p, hp_in_S, rfl⟩
        exact ⟨p, ⟨hp_in_S, h_interval⟩, by simp⟩
      · rintro ⟨p, ⟨hp_in_S, h_interval⟩, rfl⟩
        have hx_in_S' : p.1 ∈ S' := Finset.mem_image.mpr ⟨p, hp_in_S, rfl⟩
        exact ⟨hx_in_S', h_interval⟩
    rw [h_img]
    exact Finset.card_image_le
  -- Step 2: |A| ≤ 9 * C * ((M+2)*r)^s * |S|
  have h2 : (A.card : ℝ) ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) :=
    coarse_lipschitz_strip_bound hΔ_pos hs hC_pos hM_nonneg hW_nonneg
      hr_pos hW_le_r hr_ge_delta hS_sset hS_sep h_coarse (a := a)
  -- Step 3: |S| ≤ K * |S'|
  have h3 : (S.card : ℝ) ≤ K * (S'.card : ℝ) := by
    have h_sum : S.card = ∑ x ∈ S', (S.filter (fun p => p.1 = x)).card := by
      exact Finset.card_eq_sum_card_image (fun p => p.1) S
    rw [h_sum]
    have h_sum_cast : (↑(∑ x ∈ S', (S.filter (fun p => p.1 = x)).card) : ℝ) =
        ∑ x ∈ S', ((S.filter (fun p => p.1 = x)).card : ℝ) := by
      rw [Nat.cast_sum]
    rw [h_sum_cast]
    have h4 : ∀ x ∈ S', (S.filter (fun p => p.1 = x)).card ≤ K :=
      fun x _ => hK_to_one x
    have h52 : ∑ x ∈ S', ((S.filter (fun p => p.1 = x)).card : ℝ) ≤ ∑ x ∈ S', K :=
      Finset.sum_le_sum h4
    have h53 : ∑ x ∈ S', K = K * (S'.card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    rw [h53] at h52
    exact h52
  -- Combine
  have h6 : (I_set.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast h1
  have h7 : (A.card : ℝ) ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) := h2
  have h8 : (I_set.card : ℝ) ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (K * (S'.card : ℝ)) := by
    calc (I_set.card : ℝ)
      ≤ (A.card : ℝ) := h6
    _ ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (S.card : ℝ) := h7
    _ ≤ (9 : ℝ) * C * ((M + 2) * r)^s * (K * (S'.card : ℝ)) := by
      gcongr <;> linarith
  have h9 : (9 : ℝ) * C * ((M + 2) * r)^s * (K * (S'.card : ℝ)) =
      (9 : ℝ) * K * C * ((M + 2) * r)^s * (S'.card : ℝ) := by ring
  rw [h9] at h8
  exact h8

end EnergyBoundLemmas
