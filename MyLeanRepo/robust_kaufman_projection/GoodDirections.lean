module

public import MyLeanRepo.robust_kaufman_projection.Base
public import MyLeanRepo.robust_kaufman_projection.Helpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Good directions selection via finite-sum Markov argument

Selects a "good" subset of directions using a counting argument on finite sums.
Given a finite set of directions and an energy function whose sum is bounded by
`M * |S_dir|`, there exists a subset of at least half the directions for which
the energy is at most `2 * M`.

## Main results

* `good_directions_markov`: selects good directions via finite-sum averaging.
* `good_directions_cover_bound`: covering number bound (factor 6) for good directions.
-/

noncomputable section

open scoped ENNReal NNReal
open Metric Set Classical

variable {δ : ℝ}

/-! ### Covering number helper lemmas -/

/-- A closed δ-ball in ℝ contains at most 3 points of a δ-separated finset. -/
lemma closedBall_separated_card_le_three {δ : ℝ} (hδ : 0 < δ)
    {S : Set ℝ} (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    {x : ℝ} {T : Finset ℝ} (hT1 : (T : Set ℝ) ⊆ S)
    (hT2 : (T : Set ℝ) ⊆ closedBall x δ.toNNReal) :
    T.card ≤ 3 := by
  -- Every point in T is within distance δ of x
  have h_ball : ∀ y ∈ T, dist y x ≤ δ := by
    intro y hy
    have h : y ∈ closedBall x δ.toNNReal := hT2 hy
    have h' : dist y x ≤ δ ∨ y = x := by simpa [Metric.mem_closedBall] using h
    rcases h' with (h' | rfl)
    · exact h'
    · simp [hδ.le]
  -- Diameter bound: any y, z in T satisfy y - z ≤ 2δ
  have h_diam : ∀ y z, y ∈ T → z ∈ T → y - z ≤ 2 * δ := by
    intro y z hy hz
    have h1 : |y - x| ≤ δ := by simpa [Real.dist_eq] using h_ball y hy
    have h2 : |z - x| ≤ δ := by simpa [Real.dist_eq] using h_ball z hz
    have h3 : y - z ≤ |y - x| + |z - x| := by
      calc y - z
        = (y - x) + (x - z) := by ring
      _ ≤ |y - x| + |x - z| := by gcongr <;> exact le_abs_self _
      _ = |y - x| + |z - x| := by
        have h4 : |x - z| = |z - x| := abs_sub_comm x z
        rw [h4]
    linarith
  -- Suppose T.card ≥ 4, derive contradiction using sorted elements
  by_contra h
  have h4 : 4 ≤ T.card := by omega
  let L := T.sort
  have h_len : L.length = T.card := by simp [L]
  have h4' : 4 ≤ L.length := by rw [h_len]; omega
  let i0 : Fin L.length := ⟨0, by omega⟩
  let i1 : Fin L.length := ⟨1, by omega⟩
  let i2 : Fin L.length := ⟨2, by omega⟩
  let i3 : Fin L.length := ⟨3, by omega⟩
  let a := L.get i0
  let b := L.get i1
  let c := L.get i2
  let d := L.get i3
  have ha : a ∈ T := by
    have h : a ∈ L := List.mem_iff_get.mpr ⟨i0, rfl⟩
    simpa [L, Finset.mem_sort] using h
  have hb : b ∈ T := by
    have h : b ∈ L := List.mem_iff_get.mpr ⟨i1, rfl⟩
    simpa [L, Finset.mem_sort] using h
  have hc : c ∈ T := by
    have h : c ∈ L := List.mem_iff_get.mpr ⟨i2, rfl⟩
    simpa [L, Finset.mem_sort] using h
  have hd : d ∈ T := by
    have h : d ∈ L := List.mem_iff_get.mpr ⟨i3, rfl⟩
    simpa [L, Finset.mem_sort] using h
  have h_sorted : L.SortedLT := by simpa [L] using Finset.sortedLT_sort T
  have h_pairwise : L.Pairwise (· < ·) := h_sorted.pairwise
  have h_pairwise' : ∀ (i j : Fin L.length), i < j → L.get i < L.get j := by
    rwa [List.pairwise_iff_get] at h_pairwise
  have h_i0_lt_i1 : i0 < i1 := Fin.mk_lt_mk.mpr (by norm_num)
  have h_i1_lt_i2 : i1 < i2 := Fin.mk_lt_mk.mpr (by norm_num)
  have h_i2_lt_i3 : i2 < i3 := Fin.mk_lt_mk.mpr (by norm_num)
  have h_ab : a < b := h_pairwise' i0 i1 h_i0_lt_i1
  have h_bc : b < c := h_pairwise' i1 i2 h_i1_lt_i2
  have h_cd : c < d := h_pairwise' i2 i3 h_i2_lt_i3
  have h_ne_ab : a ≠ b := ne_of_lt h_ab
  have h_ne_bc : b ≠ c := ne_of_lt h_bc
  have h_ne_cd : c ≠ d := ne_of_lt h_cd
  have h_sep1 : b - a ≥ δ := by
    have h : δ ≤ |b - a| := hS b (hT1 hb) a (hT1 ha) h_ne_ab.symm
    rw [abs_of_nonneg (show 0 ≤ b - a by linarith)] at h; linarith
  have h_sep2 : c - b ≥ δ := by
    have h : δ ≤ |c - b| := hS c (hT1 hc) b (hT1 hb) h_ne_bc.symm
    rw [abs_of_nonneg (show 0 ≤ c - b by linarith)] at h; linarith
  have h_sep3 : d - c ≥ δ := by
    have h : δ ≤ |d - c| := hS d (hT1 hd) c (hT1 hc) h_ne_cd.symm
    rw [abs_of_nonneg (show 0 ≤ d - c by linarith)] at h; linarith
  have h_total : d - a ≥ 3 * δ := by linarith
  have h_ball' : d - a ≤ 2 * δ := h_diam d a hd ha
  linarith

/-- For a finite δ-separated set S, any finite cover C satisfies |S| ≤ 3 * |C|. -/
lemma separated_cover_card_le {δ : ℝ} (hδ : 0 < δ)
    {S C : Finset ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (hcover : IsCover δ.toNNReal (S : Set ℝ) (C : Set ℝ)) :
    S.card ≤ 3 * C.card := by
  let S_c : ℝ → Finset ℝ := fun c => S.filter (fun x => x ∈ closedBall c δ.toNNReal)
  have h1 : (S : Set ℝ) ⊆ ⋃ c ∈ (C : Set ℝ), closedBall c δ.toNNReal :=
    hcover.subset_iUnion_closedBall
  have h_union : (S : Set ℝ) ⊆ (C.biUnion S_c : Set ℝ) := by
    intro x hx
    have h2 : x ∈ ⋃ c ∈ (C : Set ℝ), closedBall c δ.toNNReal := h1 hx
    simp only [Set.mem_iUnion] at h2
    rcases h2 with ⟨c, hc, hxc⟩
    have h3 : c ∈ C := by exact_mod_cast hc
    have h4 : x ∈ S_c c := by
      simp only [S_c, Finset.mem_filter]
      exact ⟨hx, hxc⟩
    exact Finset.mem_biUnion.mpr ⟨c, h3, h4⟩
  have h3 : S.card ≤ (C.biUnion S_c).card := Finset.card_le_card (by exact_mod_cast h_union)
  have h4 : (C.biUnion S_c).card ≤ ∑ c ∈ C, (S_c c).card := Finset.card_biUnion_le
  have h5 : ∀ c ∈ C, (S_c c).card ≤ 3 := by
    intro c hc
    have hT1 : ((S_c c : Set ℝ)) ⊆ (S : Set ℝ) := by
      intro x hx; exact (Finset.mem_filter.mp hx).1
    have hT2 : ((S_c c : Set ℝ)) ⊆ closedBall c δ.toNNReal := by
      intro x hx; exact (Finset.mem_filter.mp hx).2
    exact closedBall_separated_card_le_three hδ hS hT1 hT2
  have h6 : ∑ c ∈ C, (S_c c).card ≤ ∑ c ∈ C, 3 := by gcongr with c hc; exact h5 c hc
  have h7 : ∑ c ∈ C, (3 : ℕ) = 3 * C.card := by
    simp [Finset.sum_const] <;> ring
  linarith

/-- For a finite δ-separated set S in ℝ, |S| ≤ 3 * Ncover δ S. -/
lemma separated_card_le_three_mul_ncover {δ : ℝ} (hδ : 0 < δ)
    {S : Finset ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (S.card : ENNReal) ≤ 3 * Ncover δ (S : Set ℝ) := by
  let ε : NNReal := δ.toNNReal
  have h_main : ∀ (C : Set ℝ), IsCover ε (S : Set ℝ) C →
      (S.card : ENNReal) ≤ 3 * (C.encard : ENNReal) := by
    intro C hC
    by_cases hfin : C.Finite
    · let C' : Finset ℝ := hfin.toFinset
      have hC' : (C' : Set ℝ) = C := by simp [C']
      have hC2 : IsCover ε (S : Set ℝ) (C' : Set ℝ) := by rw [hC']; exact hC
      have h : S.card ≤ 3 * C'.card := separated_cover_card_le hδ hS hC2
      have h_encard : (C.encard : ENNReal) = ↑(C'.card) := by
        rw [← hC'] <;> simp
      rw [h_encard]
      exact_mod_cast h
    · have hinf : C.Infinite := Set.not_finite.mp hfin
      have htop : C.encard = ⊤ := by
        simpa [Set.encard_eq_top_iff] using hinf
      have htop' : (C.encard : ENNReal) = ⊤ := by exact_mod_cast htop
      rw [htop'] <;> simp
  -- If Ncover is top, trivial
  by_cases h_top : Ncover δ (S : Set ℝ) = ⊤
  · rw [h_top] <;> simp
  · -- Ncover is finite, so externalCoveringNumber is finite
    have hfin : Metric.externalCoveringNumber ε (S : Set ℝ) ≠ ⊤ := by
      simpa [Ncover] using h_top
    -- The collection of covers is nonempty (Set.univ covers everything)
    have h_univ_cover : IsCover ε (S : Set ℝ) Set.univ := by
      intro x _
      refine ⟨x, Set.mem_univ x, ?_⟩
      simp
    haveI : Nonempty { s : Set ℝ // IsCover ε (S : Set ℝ) s } :=
      ⟨⟨Set.univ, h_univ_cover⟩⟩
    -- ENat.exists_eq_iInf gives a cover achieving the infimum
    have h_eq : (⨅ (x : { s : Set ℝ // IsCover ε (S : Set ℝ) s }), (x : Set ℝ).encard) =
        Metric.externalCoveringNumber ε (S : Set ℝ) := by
      simp_rw [Metric.externalCoveringNumber, iInf_subtype] <;> rfl
    have h_exists : ∃ (C : { s : Set ℝ // IsCover ε (S : Set ℝ) s }),
        (C : Set ℝ).encard = Metric.externalCoveringNumber ε (S : Set ℝ) := by
      let f : { s : Set ℝ // IsCover ε (S : Set ℝ) s } → ENat := fun C => (C : Set ℝ).encard
      have h : ∃ a, f a = iInf f := ENat.exists_eq_iInf f
      rcases h with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      have h_goal : f C = Metric.externalCoveringNumber ε (S : Set ℝ) := by
        rw [hC, h_eq]
      exact h_goal
    rcases h_exists with ⟨C, hC_eq⟩
    have hC_cover : IsCover ε (S : Set ℝ) (C : Set ℝ) := C.2
    have h_bound : (S.card : ENNReal) ≤ 3 * ((C : Set ℝ).encard : ENNReal) :=
      h_main (C : Set ℝ) hC_cover
    have hC_encard : ((C : Set ℝ).encard : ENNReal) = Ncover δ (S : Set ℝ) := by
      have h9 : Ncover δ (S : Set ℝ) = ↑(Metric.externalCoveringNumber ε (S : Set ℝ)) := by
        simp [Ncover] <;> rfl
      rw [h9, hC_eq]
    rw [hC_encard] at h_bound
    exact h_bound

/-! ### Main theorems -/

/-- Select good directions using a finite-sum averaging argument. -/
theorem good_directions_markov
    {S_dir : Finset ℝ} {E : ℝ → ENNReal} {M : ℝ}
    (hS_nonempty : S_dir.Nonempty)
    (hM_pos : 0 < M)
    (h_avg : ∑ σ ∈ S_dir, E σ ≤ ENNReal.ofReal M * (S_dir.card : ENNReal)) :
    ∃ (goodDirs : Finset ℝ),
      goodDirs ⊆ S_dir ∧
      (goodDirs.card : ℝ) ≥ (S_dir.card : ℝ) / 2 ∧
      ∀ σ ∈ goodDirs, E σ ≤ ENNReal.ofReal (2 * M) := by
  let threshold : ENNReal := ENNReal.ofReal (2 * M)
  let badDirs : Finset ℝ := S_dir.filter (fun σ => threshold < E σ)
  let goodDirs : Finset ℝ := S_dir \ badDirs

  have h_bad_ge : ∀ σ ∈ badDirs, threshold ≤ E σ := by
    intro σ hσ
    have h : threshold < E σ := (Finset.mem_filter.mp hσ).2
    exact le_of_lt h
  have h_bad_sum : ∑ σ ∈ badDirs, E σ ≥ threshold * (badDirs.card : ENNReal) := by
    have h1 : ∑ σ ∈ badDirs, E σ ≥ ∑ σ ∈ badDirs, threshold :=
      Finset.sum_le_sum fun i hi => h_bad_ge i hi
    have h2 : ∑ σ ∈ badDirs, threshold = threshold * (badDirs.card : ENNReal) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h1
    exact h1
  have h_bad_sub : badDirs ⊆ S_dir := Finset.filter_subset _ _
  have h_sum_mono : ∑ σ ∈ badDirs, E σ ≤ ∑ σ ∈ S_dir, E σ :=
    Finset.sum_le_sum_of_subset_of_nonneg h_bad_sub (fun _ _ _ => by positivity)
  have h5 : threshold * (badDirs.card : ENNReal) ≤ ∑ σ ∈ S_dir, E σ :=
    le_trans h_bad_sum h_sum_mono
  have h6 : threshold * (badDirs.card : ENNReal) ≤ ENNReal.ofReal M * (S_dir.card : ENNReal) :=
    le_trans h5 h_avg
  have hM_pos' : ENNReal.ofReal M ≠ 0 := by positivity
  have hM_top : ENNReal.ofReal M ≠ ⊤ := by simp
  have h_thresh_eq : threshold = 2 * ENNReal.ofReal M := by
    simp [threshold, ENNReal.ofReal_mul] <;> ring
  rw [h_thresh_eq] at h6
  -- Cancel ENNReal.ofReal M from both sides
  have h7 : 2 * (badDirs.card : ENNReal) ≤ (S_dir.card : ENNReal) := by
    have h6' : ENNReal.ofReal M * (2 * (badDirs.card : ENNReal)) ≤
        ENNReal.ofReal M * (S_dir.card : ENNReal) := by
      have h_comm : (2 * ENNReal.ofReal M) * (badDirs.card : ENNReal) =
          ENNReal.ofReal M * (2 * (badDirs.card : ENNReal)) := by
        simp [mul_comm, mul_assoc, mul_left_comm]
      rw [h_comm] at h6
      exact h6
    have h_iff : ENNReal.ofReal M * (2 * (badDirs.card : ENNReal)) ≤
        ENNReal.ofReal M * (S_dir.card : ENNReal) ↔
        2 * (badDirs.card : ENNReal) ≤ (S_dir.card : ENNReal) :=
      ENNReal.mul_le_mul_iff_right hM_pos' hM_top
    exact h_iff.mp h6'
  have h8 : 2 * badDirs.card ≤ S_dir.card := by exact_mod_cast h7
  have h9 : goodDirs.card = S_dir.card - badDirs.card := by
    have h_card : (S_dir \ badDirs).card = S_dir.card - (badDirs ∩ S_dir).card := Finset.card_sdiff
    have h_inter : badDirs ∩ S_dir = badDirs := by
      apply Finset.inter_eq_left.mpr; exact h_bad_sub
    simpa [goodDirs, h_inter] using h_card
  have h10 : 2 * goodDirs.card ≥ S_dir.card := by
    rw [h9]; omega
  have h11 : (goodDirs.card : ℝ) ≥ (S_dir.card : ℝ) / 2 := by
    have h12 : 2 * (goodDirs.card : ℝ) ≥ (S_dir.card : ℝ) := by exact_mod_cast h10
    linarith
  have h_good_prop : ∀ σ ∈ goodDirs, E σ ≤ threshold := by
    intro σ hσ
    have h13 : σ ∉ badDirs := (Finset.mem_sdiff.mp hσ).2
    have h14 : σ ∈ S_dir := (Finset.mem_sdiff.mp hσ).1
    have h15 : ¬(threshold < E σ) := by
      by_contra h16
      exact h13 (Finset.mem_filter.mpr ⟨h14, h16⟩)
    exact le_of_not_gt h15
  have h_sub : goodDirs ⊆ S_dir := Finset.sdiff_subset
  exact ⟨goodDirs, h_sub, h11, h_good_prop⟩

/-- Covering number bound for good directions (factor 6). -/
lemma good_directions_cover_bound
    {S_dir goodDirs : Finset ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hS_dir_sep : ∀ σ ∈ S_dir, ∀ τ ∈ S_dir, σ ≠ τ → δ ≤ |σ - τ|)
    (hgood_sub : goodDirs ⊆ S_dir)
    (hgood_card : (goodDirs.card : ℝ) ≥ (S_dir.card : ℝ) / 2) :
    Ncover δ (S_dir : Set ℝ) ≤ 6 * Ncover δ (goodDirs : Set ℝ) := by
  have hgood_sep : ∀ x ∈ goodDirs, ∀ y ∈ goodDirs, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hne
    exact hS_dir_sep x (hgood_sub hx) y (hgood_sub hy) hne
  have h1 : Ncover δ (S_dir : Set ℝ) ≤ (S_dir.card : ENNReal) := by
    have h : Metric.externalCoveringNumber δ.toNNReal (S_dir : Set ℝ) ≤ (S_dir : Set ℝ).encard :=
      Metric.externalCoveringNumber_le_encard_self (S_dir : Set ℝ)
    have h' : (S_dir : Set ℝ).encard = ↑(S_dir.card) := by simp
    have h'' : (Metric.externalCoveringNumber δ.toNNReal (S_dir : Set ℝ) : ENNReal) ≤ ((S_dir : Set ℝ).encard : ENNReal) := by
      exact_mod_cast h
    rw [h'] at h''
    simpa [Ncover] using h''
  have h2 : 2 * goodDirs.card ≥ S_dir.card := by
    have h2' : 2 * (goodDirs.card : ℝ) ≥ (S_dir.card : ℝ) := by linarith
    exact_mod_cast h2'
  have h3 : (S_dir.card : ENNReal) ≤ 2 * (goodDirs.card : ENNReal) := by
    exact_mod_cast h2
  have h4 : (goodDirs.card : ENNReal) ≤ 3 * Ncover δ (goodDirs : Set ℝ) := by
    exact separated_card_le_three_mul_ncover hδ hgood_sep
  calc Ncover δ (S_dir : Set ℝ)
    ≤ (S_dir.card : ENNReal) := h1
    _ ≤ 2 * (goodDirs.card : ENNReal) := h3
    _ ≤ 2 * (3 * Ncover δ (goodDirs : Set ℝ)) := by gcongr
    _ = 6 * Ncover δ (goodDirs : Set ℝ) := by ring

/-! ### Factor-2 version using strict 2δ-separated witness -/

/-- Factor-2 good directions: given a strict 2δ-separated covering witness R,
select a good subset achieving factor 2 in covering number. -/
theorem good_directions_factor2
    {directions : Set ℝ} {δ : ℝ} {E : ℝ → ENNReal} {M : ℝ}
    (hδ : 0 < δ) (hM_pos : 0 < M)
    (R : Finset ℝ)
    (hR_sub : (R : Set ℝ) ⊆ directions)
    (hR_sep : ∀ x ∈ R, ∀ y ∈ R, x ≠ y → 2 * δ < |x - y|)
    (hR_card : Ncover δ directions = (R.card : ENNReal))
    (h_avg : ∑ σ ∈ R, E σ ≤ ENNReal.ofReal M * (R.card : ENNReal)) :
    ∃ goodDirections : Set ℝ,
      goodDirections ⊆ directions ∧
      Ncover δ directions ≤ 2 * Ncover δ goodDirections ∧
      ∀ σ ∈ goodDirections, E σ ≤ ENNReal.ofReal (2 * M) := by
  by_cases hR_empty : R = ∅
  · -- R empty ⇒ Ncover δ directions = 0, so goodDirections = ∅ works
    have h_ncover_zero : Ncover δ directions = 0 := by
      rw [hR_empty] at hR_card; simpa using hR_card
    have h_ncover_empty : Ncover δ (∅ : Set ℝ) = 0 := by
      rw [Ncover, Metric.externalCoveringNumber_eq_zero.mpr rfl]
      <;> simp
    refine ⟨(∅ : Set ℝ), by simp, ?_, by simp⟩
    rw [h_ncover_empty]
    simpa using h_ncover_zero
  · -- R nonempty: apply Markov then use strict 2δ-separation for factor 2
    have hR_nonempty : R.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hR_empty
    have h_markov := good_directions_markov hR_nonempty hM_pos h_avg
    rcases h_markov with ⟨goodDirs, hgood_sub_R, hgood_card, hgood_E⟩
    -- goodDirs inherits strict 2δ-separation from R
    have hgood_sep : ∀ x ∈ goodDirs, ∀ y ∈ goodDirs, x ≠ y → 2 * δ < |x - y| := by
      intro x hx y hy hne
      exact hR_sep x (hgood_sub_R hx) y (hgood_sub_R hy) hne
    -- Ncover δ goodDirs = |goodDirs| (strict 2δ-separated)
    have h_ncover_good : Ncover δ (goodDirs : Set ℝ) = (goodDirs.card : ENNReal) :=
      ncover_eq_card_of_two_delta_separated hδ hgood_sep
    -- goodDirs ⊆ R ⊆ directions
    have hgood_sub_dir : (goodDirs : Set ℝ) ⊆ directions :=
      Set.Subset.trans (by exact_mod_cast hgood_sub_R) hR_sub
    -- |R| ≤ 2|goodDirs|
    have h_card_real : 2 * (goodDirs.card : ℝ) ≥ (R.card : ℝ) := by
      have h : (goodDirs.card : ℝ) ≥ (R.card : ℝ) / 2 := hgood_card
      linarith
    have h_card_nat : 2 * goodDirs.card ≥ R.card := by exact_mod_cast h_card_real
    have h_card' : (R.card : ENNReal) ≤ 2 * (goodDirs.card : ENNReal) := by
      exact_mod_cast h_card_nat
    -- Main inequality
    have h_main : Ncover δ directions ≤ 2 * Ncover δ (goodDirs : Set ℝ) := by
      calc Ncover δ directions
        = (R.card : ENNReal) := hR_card
      _ ≤ 2 * (goodDirs.card : ENNReal) := h_card'
      _ = 2 * Ncover δ (goodDirs : Set ℝ) := by rw [h_ncover_good]
    exact ⟨(goodDirs : Set ℝ), hgood_sub_dir, h_main, hgood_E⟩
