/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.LooseUniformAnchorNet

/-!
# J1 — the two-partition regulariser: one subfamily carrying both Definition-2.2 data

Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations` asks for a **loose** GWZ Definition-2.2 datum
(`Kakeya.LooseUniform.LooseShadedUniformTubeSet`) on the configuration's family `cfg.s`, while the
configuration's own field `Kakeya.VeryNotSticky.uniform` is an **exact** one
(`ShadedTube.ShadedUniformTubeSet`) on the same `cfg.s`.   measured that the
two hierarchies refine each other in neither direction (an exact class is axially localised, an
anchored loose class is axially spread by `Θ(1)`), so the existing pruning engine
`Tube.exists_pruned_subset_noroot_notop` — which brackets exactly the classes of the *one* nested
tower it is given — cannot band both at once, and the alternating tower fails its `h_nested`.

This file builds the missing engine **without any nesting**, and it is elementary:

* **Type pigeonhole** (`exists_dyType_fiber`).  Fix the dyadic class `⌊log₂ |class|⌋` of every
  member along *every* partition of a finite family `J` of partitions at once: one of the
  `≤ (L+1)^{|J|}` types carries a `(L+1)^{-|J|}` share of the family.
* **Peeling** (`exists_good_subset`).  Repeatedly delete any class that has fallen below its
  threshold `2^{a_j}/K`.  Each deletion kills one label for good, and every label of the chosen
  type had a class of size `≥ 2^{a_j}` in the original family, so there are at most `|U|/2^{a_j}`
  labels per partition and the total loss is at most `|J| · |U| / K` — half the type class at
  `K = 2 |J| (L+1)^{|J|}`.  The survivors are banded on every partition:
  `2^{a_j} / (2K) ≤ |class| < 2^{a_j + 1}` (`exists_multi_regular`).
* **Two towers** (`exists_two_tower_regular`): the specialisation to `J = {exact, loose} × {0..M}`.
  The band constant is `twoTowerConst M L = 8 (M+1) (L+1)^{2M+2}`, and the retention is
  `2 (L+1)^{2M+2}`; both are `≤ (8 (L+1))^{2M+2}`, the shape
  `Tube.exists_threshold_polylog_pow_ssfGridLen_le` absorbs into `δ^{-α}` at the grid length
  `Tube.ssfGridLen δ`.

The price of nesting-freedom is that the band constant is polylogarithmic in `|s|` rather than
`2`; at the grid length `N = ⌈log log 1/δ⌉` it is `(log 1/δ)^{O(log log 1/δ)} = δ^{o(1)}`, which
is all any Section-9 consumer asks (`1 ≤ C ≤ δ^{-η}`).

On top of the abstract engine:

* `exists_joint_uniform_subfamily` — GWZ Definition 2.1 in **both** models on one subfamily
  (the exact cover is inherited from a given `Tube.UniformTubeSet`, the loose one is the existing
  anchored cover `Kakeya.LooseUniform.exists_looseGridCover` at retention `1`);
* `exists_joint_shadeRefinement` — GWZ Definition 2.2's shade brackets for both towers at once
  (the per-fibre two-tower regularisation, then one profile pigeonhole over points; a
  re-implementation of the private stage machinery of `Kakeya/ShadedUniform.lean` because that
  machinery is `private`);
* `exists_joint_refinement` — **the deliverable**: at `N = Tube.ssfGridLen δ`, from an exact
  Definition-2.2 datum on `(s, V)` with `|s| ≤ δ^{-K₀}`, a refinement `(s', V')` (index subset,
  tubes unchanged, shades shrunk, cardinality retained up to `δ^{-α}`, fullness up to `δ^{-α'}`)
  carrying both `ShadedTube.ShadedUniformTubeSet s' V' N C` and
  `Kakeya.LooseUniform.LooseShadedUniformTubeSet s' V' N 4 C` at one common constant
  `C = jointConst C₀ Cj`, `Cj ≤ δ^{-α}`.

Nothing here touches a protected statement, and nothing from the Section-8 directory is read.
The honest reading, including what remains for the configuration twin (J4) and the parent side
(J5), is .
-/

@[expose] public section

open Finset

namespace Kakeya.JointRefine

variable {ι κ : Type*}

/-! ### Classes -/

theorem mem_coverClass_self (U : Finset ι) (f : ι → ι) {i : ι} (hi : i ∈ U) :
    i ∈ Tube.coverClass U f (f i) := by
  classical
  simp [Tube.coverClass, hi]

theorem coverClass_subset (U : Finset ι) (f : ι → ι) (p : ι) : Tube.coverClass U f p ⊆ U := by
  classical
  intro j hj
  exact (Finset.mem_filter.mp hj).1

theorem coverClass_card_pos (U : Finset ι) (f : ι → ι) {i : ι} (hi : i ∈ U) :
    0 < (Tube.coverClass U f (f i)).card :=
  Finset.card_pos.mpr ⟨i, mem_coverClass_self U f hi⟩

theorem mem_coverClass_iff (U : Finset ι) (f : ι → ι) (p j : ι) :
    j ∈ Tube.coverClass U f p ↔ j ∈ U ∧ f j = p := by
  classical
  simp [Tube.coverClass]

/-- The class sizes over any set of labels sum to at most `|U|`. -/
theorem sum_card_coverClass_le (U : Finset ι) (f : ι → ι) (t : Finset ι) :
    ∑ p ∈ t, (Tube.coverClass U f p).card ≤ U.card := by
  classical
  have hdisj : (t : Set ι).PairwiseDisjoint (fun p => Tube.coverClass U f p) := by
    intro p _ q _ hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro i hip hiq
    exact hpq (((mem_coverClass_iff U f p i).mp hip).2.symm.trans
      ((mem_coverClass_iff U f q i).mp hiq).2)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr fun p _ => coverClass_subset U f p)

/-! ### The dyadic type of a member along a finite family of partitions -/

/-- The dyadic type of `i` in `U`: the vector of `⌊log₂⌋` of its class sizes along the
partitions indexed by `J`. -/
noncomputable def dyType (U : Finset ι) (f : κ → ι → ι) (J : Finset κ) (i : ι) : J → ℕ :=
  fun j => Nat.log 2 (Tube.coverClass U (f j) (f j i)).card

theorem dyType_mem_piFinset [DecidableEq κ] (U : Finset ι) (f : κ → ι → ι) (J : Finset κ) {L : ℕ}
    (hL : Nat.log 2 U.card ≤ L) (i : ι) :
    dyType U f J i ∈ Fintype.piFinset (fun _ : J => Finset.range (L + 1)) := by
  classical
  rw [Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (Nat.log_mono_right (Finset.card_le_card (coverClass_subset U (f j) _))).trans hL

theorem card_piFinset_range [DecidableEq κ] (J : Finset κ) (L : ℕ) :
    (Fintype.piFinset (fun _ : J => Finset.range (L + 1))).card = (L + 1) ^ J.card := by
  classical
  rw [Fintype.card_piFinset]
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- **Type pigeonhole.**  One dyadic type carries a `(L+1)^{-|J|}` share of `U`. -/
theorem exists_dyType_fiber (U : Finset ι) (hU : U.Nonempty) (f : κ → ι → ι)
    (J : Finset κ) {L : ℕ} (hL : Nat.log 2 U.card ≤ L) :
    ∃ p : J → ℕ, (∀ j, p j ≤ L) ∧
      (U.filter (fun i => dyType U f J i = p)).Nonempty ∧
      (U.card : ℝ) ≤ (L + 1 : ℝ) ^ J.card
        * ((U.filter (fun i => dyType U f J i = p)).card : ℝ) := by
  classical
  set Tset := Fintype.piFinset (fun _ : J => Finset.range (L + 1)) with hTset
  have hmaps : ∀ i ∈ U, dyType U f J i ∈ Tset := fun i _ => dyType_mem_piFinset U f J hL i
  have hsum : U.card = ∑ p ∈ Tset, (U.filter (fun i => dyType U f J i = p)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  obtain ⟨i₀, hi₀⟩ := hU
  have hTne : Tset.Nonempty := ⟨_, hmaps i₀ hi₀⟩
  have hTpos : (0 : ℝ) < Tset.card := by exact_mod_cast Finset.card_pos.mpr hTne
  have hcardT : Tset.card = (L + 1) ^ J.card := card_piFinset_range J L
  obtain ⟨p, hp, hle⟩ := Finset.exists_le_of_sum_le hTne
    (f := fun _ => (U.card : ℝ) / Tset.card)
    (g := fun p => ((U.filter (fun i => dyType U f J i = p)).card : ℝ)) (by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hTpos.ne']
      rw [hsum]; push_cast; exact le_rfl)
  have hpL : ∀ j, p j ≤ L := fun j =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hp j))
  have hUle : (U.card : ℝ) ≤ (L + 1 : ℝ) ^ J.card
      * ((U.filter (fun i => dyType U f J i = p)).card : ℝ) := by
    rw [div_le_iff₀ hTpos] at hle
    calc (U.card : ℝ) ≤ _ * (Tset.card : ℝ) := hle
      _ = (L + 1 : ℝ) ^ J.card * _ := by rw [hcardT]; push_cast; ring
  refine ⟨p, hpL, ?_, hUle⟩
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  rw [hne] at hUle
  simp at hUle
  simp [hUle] at hi₀

/-! ### Peeling -/

/-- `G` is *good* for the thresholds `t`: along every partition in `J`, every class of `G`
has at least `t j` members. -/
def Good (f : κ → ι → ι) (t : κ → ℕ) (J : Finset κ) (G : Finset ι) : Prop :=
  ∀ j ∈ J, ∀ i ∈ G, t j ≤ (Tube.coverClass G (f j) (f j i)).card

/-- The peeling potential: thresholds times the number of labels in use. -/
def peelSum [DecidableEq ι] (f : κ → ι → ι) (t : κ → ℕ) (J : Finset κ) (U : Finset ι) : ℕ :=
  ∑ j ∈ J, t j * (U.image (f j)).card

/-- **Peeling.**  Deleting undersized classes until none is left costs at most the potential. -/
theorem exists_good_subset [DecidableEq ι] (f : κ → ι → ι) (t : κ → ℕ)
    (J : Finset κ) (U : Finset ι) :
    ∃ G ⊆ U, Good f t J G ∧ U.card ≤ G.card + peelSum f t J U := by
  classical
  induction U using Finset.strongInduction with
  | H U ih =>
    by_cases hgood : Good f t J U
    · exact ⟨U, Finset.Subset.refl _, hgood, Nat.le_add_right _ _⟩
    · simp only [Good, not_forall, not_le] at hgood
      obtain ⟨j, hj, i, hi, hlt⟩ := hgood
      set cls := Tube.coverClass U (f j) (f j i) with hcls
      set U' := U \ cls with hU'
      have hclsU : cls ⊆ U := coverClass_subset U (f j) _
      have hU'sub : U' ⊆ U := Finset.sdiff_subset
      have hiU' : i ∉ U' := fun h => (Finset.mem_sdiff.mp h).2 (mem_coverClass_self U (f j) hi)
      have hss : U' ⊂ U := (Finset.ssubset_iff_of_subset hU'sub).mpr ⟨i, hi, hiU'⟩
      obtain ⟨G, hGU', hGgood, hGcard⟩ := ih U' hss
      refine ⟨G, hGU'.trans hU'sub, hGgood, ?_⟩
      have hsplit : U'.card + cls.card = U.card := Finset.card_sdiff_add_card_eq_card hclsU
      have himg : U'.image (f j) ⊂ U.image (f j) := by
        rw [Finset.ssubset_iff_of_subset (Finset.image_subset_image hU'sub)]
        refine ⟨f j i, Finset.mem_image_of_mem _ hi, ?_⟩
        intro h
        obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
        have hxU' := Finset.mem_sdiff.mp hx
        exact hxU'.2 ((mem_coverClass_iff U (f j) (f j i) x).mpr ⟨hxU'.1, hxe⟩)
      have himgc : (U'.image (f j)).card + 1 ≤ (U.image (f j)).card := Finset.card_lt_card himg
      have hpeel : peelSum f t J U' + t j ≤ peelSum f t J U := by
        unfold peelSum
        rw [← Finset.add_sum_erase J _ hj, ← Finset.add_sum_erase J _ hj]
        have h1 : ∑ x ∈ J.erase j, t x * (U'.image (f x)).card
            ≤ ∑ x ∈ J.erase j, t x * (U.image (f x)).card :=
          Finset.sum_le_sum fun x _ =>
            Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.image_subset_image hU'sub))
        have h2 : t j * (U'.image (f j)).card + t j ≤ t j * (U.image (f j)).card := by
          calc t j * (U'.image (f j)).card + t j = t j * ((U'.image (f j)).card + 1) := by ring
            _ ≤ t j * (U.image (f j)).card := Nat.mul_le_mul_left _ himgc
        omega
      omega

/-! ### The regularisation -/

/-- The lower-bracket constant of the multi-partition regularisation of `P` partitions at
the logarithmic clamp `L`. -/
def regConst (P L : ℕ) : ℕ := 4 * P * (L + 1) ^ P

theorem two_le_regConst {P L : ℕ} (hP : 0 < P) : 2 ≤ regConst P L := by
  unfold regConst
  have h1 : 1 ≤ (L + 1) ^ P := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- **Simultaneous regularisation of finitely many partitions.**  Any nonempty `U` has a
subset `G` retaining a `1 / (2 (L+1)^{|J|})` share on which, along *every* partition in `J`,
the classes are banded: `2^{a j} / regConst ≤ |class| < 2^{a j + 1}`.  No nesting between the
partitions is assumed. -/
theorem exists_multi_regular (f : κ → ι → ι) (J : Finset κ)
    (U : Finset ι) (hU : U.Nonempty) {L : ℕ} (hL : Nat.log 2 U.card ≤ L) :
    ∃ (G : Finset ι) (a : κ → ℕ), G ⊆ U ∧ G.Nonempty ∧
      (U.card : ℝ) ≤ 2 * (L + 1 : ℝ) ^ J.card * (G.card : ℝ) ∧
      (∀ j ∈ J, a j ≤ L) ∧
      (∀ j ∈ J, ∀ i ∈ G,
        2 ^ a j ≤ regConst J.card L * (Tube.coverClass G (f j) (f j i)).card ∧
        (Tube.coverClass G (f j) (f j i)).card < 2 ^ (a j + 1)) := by
  classical
  obtain ⟨p, hpL, hτne, hUτ⟩ := exists_dyType_fiber U hU f J hL
  set Uτ := U.filter (fun i => dyType U f J i = p) with hUτdef
  have hUτsub : Uτ ⊆ U := Finset.filter_subset _ _
  set a : κ → ℕ := fun j => if h : j ∈ J then p ⟨j, h⟩ else 0 with ha
  have ha_mem : ∀ j (hj : j ∈ J), a j = p ⟨j, hj⟩ := fun j hj => by simp [ha, hj]
  have htype : ∀ j ∈ J, ∀ i ∈ Uτ,
      2 ^ a j ≤ (Tube.coverClass U (f j) (f j i)).card ∧
      (Tube.coverClass U (f j) (f j i)).card < 2 ^ (a j + 1) := by
    intro j hj i hi
    have hi' := Finset.mem_filter.mp hi
    have hlog : Nat.log 2 (Tube.coverClass U (f j) (f j i)).card = a j := by
      rw [ha_mem j hj, ← hi'.2]; rfl
    have hne : (Tube.coverClass U (f j) (f j i)).card ≠ 0 :=
      (coverClass_card_pos U (f j) hi'.1).ne'
    refine ⟨?_, ?_⟩
    · rw [← hlog]; exact Nat.pow_log_le_self 2 hne
    · rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  set Kc : ℕ := 2 * J.card * (L + 1) ^ J.card with hKc
  set t : κ → ℕ := fun j => 2 ^ a j / Kc with ht
  obtain ⟨G, hGU, hGgood, hGcard⟩ := exists_good_subset f t J Uτ
  have hterm : ∀ j ∈ J, (t j : ℝ) * ((Uτ.image (f j)).card : ℝ) ≤ (U.card : ℝ) / Kc := by
    intro j hj
    have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨j, hj⟩
    have hKcpos : (0 : ℝ) < Kc := by
      rw [hKc]; push_cast; positivity
    have himg : (2 ^ a j : ℝ) * ((Uτ.image (f j)).card : ℝ) ≤ (U.card : ℝ) := by
      have h1 : ∑ _q ∈ Uτ.image (f j), (2 : ℕ) ^ a j
          ≤ ∑ q ∈ Uτ.image (f j), (Tube.coverClass U (f j) q).card := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (htype j hj i hi).1
      have h2 := sum_card_coverClass_le U (f j) (Uτ.image (f j))
      have h3 : (Uτ.image (f j)).card * 2 ^ a j ≤ U.card := by
        rw [Finset.sum_const, smul_eq_mul] at h1
        exact h1.trans h2
      have h3' : (((Uτ.image (f j)).card : ℝ) * (2 : ℝ) ^ a j) ≤ (U.card : ℝ) := by
        exact_mod_cast h3
      linarith [h3']
    have htK : (t j : ℝ) ≤ (2 ^ a j : ℝ) / Kc := by
      have := Nat.cast_div_le (α := ℝ) (m := 2 ^ a j) (n := Kc)
      simpa [ht] using this
    calc (t j : ℝ) * ((Uτ.image (f j)).card : ℝ)
        ≤ ((2 ^ a j : ℝ) / Kc) * ((Uτ.image (f j)).card : ℝ) :=
          mul_le_mul_of_nonneg_right htK (by positivity)
      _ = ((2 ^ a j : ℝ) * ((Uτ.image (f j)).card : ℝ)) / Kc := by ring
      _ ≤ (U.card : ℝ) / Kc := div_le_div_of_nonneg_right himg hKcpos.le
  have hpeel : (peelSum f t J Uτ : ℝ) ≤ (Uτ.card : ℝ) / 2 := by
    rcases J.eq_empty_or_nonempty with hJ | hJne
    · simp only [peelSum, hJ, Finset.sum_empty, Nat.cast_zero]
      positivity
    have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
    have hKcpos : (0 : ℝ) < Kc := by
      rw [hKc]; push_cast; positivity
    have hLpos : (0 : ℝ) < (L + 1 : ℝ) ^ J.card := by positivity
    calc (peelSum f t J Uτ : ℝ) = ∑ j ∈ J, (t j : ℝ) * ((Uτ.image (f j)).card : ℝ) := by
          rw [peelSum]; push_cast; rfl
      _ ≤ ∑ _j ∈ J, (U.card : ℝ) / Kc := Finset.sum_le_sum hterm
      _ = J.card * ((U.card : ℝ) / Kc) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (U.card : ℝ) / (2 * (L + 1 : ℝ) ^ J.card) := by
          rw [hKc]; push_cast
          have hJne' : (J.card : ℝ) ≠ 0 := by exact_mod_cast hJpos.ne'
          field_simp
      _ ≤ (Uτ.card : ℝ) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hUτ]
  have hGhalf : (Uτ.card : ℝ) / 2 ≤ (G.card : ℝ) := by
    have h : (Uτ.card : ℝ) ≤ G.card + peelSum f t J Uτ := by exact_mod_cast hGcard
    linarith
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    have hτpos : (0 : ℝ) < Uτ.card := by exact_mod_cast Finset.card_pos.mpr hτne
    have : (0 : ℝ) < G.card := by linarith
    exact_mod_cast this
  refine ⟨G, a, hGU.trans hUτsub, hGne, ?_, fun j hj => (ha_mem j hj) ▸ hpL ⟨j, hj⟩, ?_⟩
  · calc (U.card : ℝ) ≤ (L + 1 : ℝ) ^ J.card * Uτ.card := hUτ
      _ ≤ (L + 1 : ℝ) ^ J.card * (2 * G.card) := by gcongr; linarith
      _ = 2 * (L + 1 : ℝ) ^ J.card * G.card := by ring
  · intro j hj i hi
    have hiτ : i ∈ Uτ := hGU hi
    refine ⟨?_, ?_⟩
    · have hgood := hGgood j hj i hi
      have hpos : 0 < (Tube.coverClass G (f j) (f j i)).card := coverClass_card_pos G (f j) hi
      have hJpos : 0 < J.card := Finset.card_pos.mpr ⟨j, hj⟩
      have hKcpos : 0 < Kc := by
        rw [hKc]; positivity
      have hreg : regConst J.card L = 2 * Kc := by rw [regConst, hKc]; ring
      rw [hreg]
      by_cases hsmall : 2 ^ a j < Kc
      · calc 2 ^ a j ≤ Kc := hsmall.le
          _ ≤ 2 * Kc * 1 := by omega
          _ ≤ 2 * Kc * (Tube.coverClass G (f j) (f j i)).card := Nat.mul_le_mul_left _ hpos
      · rw [not_lt] at hsmall
        have hq : 1 ≤ 2 ^ a j / Kc := (Nat.one_le_div_iff hKcpos).mpr hsmall
        have hlt := Nat.lt_div_mul_add (a := 2 ^ a j) hKcpos
        have hKq : Kc ≤ 2 ^ a j / Kc * Kc := by nlinarith
        calc 2 ^ a j ≤ 2 ^ a j / Kc * Kc + Kc := hlt.le
          _ ≤ 2 ^ a j / Kc * Kc + 2 ^ a j / Kc * Kc := by omega
          _ = 2 * Kc * (2 ^ a j / Kc) := by ring
          _ ≤ 2 * Kc * (Tube.coverClass G (f j) (f j i)).card := Nat.mul_le_mul_left _ hgood
    · exact lt_of_le_of_lt
        (Finset.card_le_card (Tube.coverClass_subset_of_subset (hGU.trans hUτsub) _ _))
        (htype j hj i hiτ).2

/-! ### Two towers -/

/-- The index set of two towers of `M + 1` levels each. -/
def twoTowerIndex (M : ℕ) : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (M + 1)

theorem card_twoTowerIndex (M : ℕ) : (twoTowerIndex M).card = 2 * (M + 1) := by
  simp [twoTowerIndex, Finset.card_product]

theorem mem_twoTowerIndex {M : ℕ} (b : Bool) {k : ℕ} (hk : k ≤ M) : (b, k) ∈ twoTowerIndex M := by
  simp [twoTowerIndex, hk]

/-- The two towers as one family of partitions. -/
def twoTower (ea la : ℕ → ι → ι) : Bool × ℕ → ι → ι :=
  fun bk => if bk.1 then ea bk.2 else la bk.2

@[simp] theorem twoTower_true (ea la : ℕ → ι → ι) (k : ℕ) : twoTower ea la (true, k) = ea k := rfl
@[simp] theorem twoTower_false (ea la : ℕ → ι → ι) (k : ℕ) : twoTower ea la (false, k) = la k := rfl

/-- The band constant of the two-tower regularisation over `M + 1` levels. -/
def twoTowerConst (M L : ℕ) : ℕ := regConst (2 * (M + 1)) L

theorem two_le_twoTowerConst (M L : ℕ) : 2 ≤ twoTowerConst M L :=
  two_le_regConst (by omega)

/-- **Two nested towers, regularised at once.**  No relation between the towers is used. -/
theorem exists_two_tower_regular (ea la : ℕ → ι → ι) (M : ℕ) (U : Finset ι)
    (hU : U.Nonempty) {L : ℕ} (hL : Nat.log 2 U.card ≤ L) :
    ∃ (G : Finset ι) (ae al : ℕ → ℕ), G ⊆ U ∧ G.Nonempty ∧
      (U.card : ℝ) ≤ 2 * (L + 1 : ℝ) ^ (2 * (M + 1)) * (G.card : ℝ) ∧
      (∀ k ≤ M, ae k ≤ L ∧ al k ≤ L) ∧
      (∀ k ≤ M, ∀ i ∈ G,
        2 ^ ae k ≤ twoTowerConst M L * (Tube.coverClass G (ea k) (ea k i)).card ∧
        (Tube.coverClass G (ea k) (ea k i)).card < 2 ^ (ae k + 1)) ∧
      (∀ k ≤ M, ∀ i ∈ G,
        2 ^ al k ≤ twoTowerConst M L * (Tube.coverClass G (la k) (la k i)).card ∧
        (Tube.coverClass G (la k) (la k i)).card < 2 ^ (al k + 1)) := by
  classical
  obtain ⟨G, a, hGU, hGne, hcard, haL, hband⟩ :=
    exists_multi_regular (twoTower ea la) (twoTowerIndex M) U hU hL
  rw [card_twoTowerIndex] at hcard hband
  refine ⟨G, fun k => a (true, k), fun k => a (false, k), hGU, hGne, hcard, ?_, ?_, ?_⟩
  · intro k hk
    exact ⟨haL _ (mem_twoTowerIndex true hk), haL _ (mem_twoTowerIndex false hk)⟩
  · intro k hk i hi
    simpa [twoTowerConst] using hband (true, k) (mem_twoTowerIndex true hk) i hi
  · intro k hk i hi
    simpa [twoTowerConst] using hband (false, k) (mem_twoTowerIndex false hk) i hi

/-- The two-tower constants against the standard polylogarithmic shape. -/
theorem twoTowerConst_le (M L : ℕ) :
    (twoTowerConst M L : ℝ) ≤ (8 * ((L : ℝ) + 1)) ^ (2 * M + 2) := by
  have hM : (M : ℝ) + 1 ≤ (8 : ℝ) ^ M := by
    have h : M + 1 ≤ 8 ^ M := by
      have h2 : M < 2 ^ M := Nat.lt_two_pow_self
      have h8 : 2 ^ M ≤ 8 ^ M := Nat.pow_le_pow_left (by norm_num) M
      omega
    exact_mod_cast h
  have hL : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  unfold twoTowerConst regConst
  push_cast
  have e1 : (8 : ℝ) ^ (2 * M + 2) = 8 * 8 ^ M * 8 ^ (M + 1) := by ring
  calc (4 : ℝ) * (2 * ((M : ℝ) + 1)) * ((L : ℝ) + 1) ^ (2 * (M + 1))
      = 8 * ((M : ℝ) + 1) * ((L : ℝ) + 1) ^ (2 * M + 2) := by ring_nf
    _ ≤ 8 * (8 : ℝ) ^ M * ((L : ℝ) + 1) ^ (2 * M + 2) := by gcongr
    _ = 8 * (8 : ℝ) ^ M * ((L : ℝ) + 1) ^ (2 * M + 2) * 1 := (mul_one _).symm
    _ ≤ 8 * (8 : ℝ) ^ M * ((L : ℝ) + 1) ^ (2 * M + 2) * 8 ^ (M + 1) := by
        have : (1 : ℝ) ≤ 8 ^ (M + 1) := one_le_pow₀ (by norm_num)
        exact mul_le_mul_of_nonneg_left this (by positivity)
    _ = 8 * (8 : ℝ) ^ M * 8 ^ (M + 1) * ((L : ℝ) + 1) ^ (2 * M + 2) := by ring
    _ = (8 * ((L : ℝ) + 1)) ^ (2 * M + 2) := by rw [mul_pow, ← e1]

theorem two_mul_pow_le (M L : ℕ) :
    (2 : ℝ) * ((L : ℝ) + 1) ^ (2 * (M + 1)) ≤ (8 * ((L : ℝ) + 1)) ^ (2 * M + 2) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  have h2 : (2 : ℝ) ≤ 8 ^ (2 * M + 2) := by
    calc (2 : ℝ) ≤ 8 := by norm_num
      _ = 8 ^ 1 := (pow_one _).symm
      _ ≤ 8 ^ (2 * M + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [mul_pow, show 2 * (M + 1) = 2 * M + 2 by ring]
  exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hL _)


/-! ### J1 at the tube level: both Definition-2.1 data on one subfamily -/

section TubeLevel

open Kakeya.LooseUniform

theorem band_upper_nnreal {c a K : ℕ} (hK : 2 ≤ K) (h : c < 2 ^ (a + 1)) :
    (c : NNReal) ≤ (K : NNReal) * (2 : NNReal) ^ a := by
  have h1 : c ≤ 2 * 2 ^ a := by rw [pow_succ] at h; omega
  have h2 : c ≤ K * 2 ^ a := h1.trans (Nat.mul_le_mul_right _ hK)
  exact_mod_cast h2

theorem band_lower_nnreal {c a K : ℕ} (h : 2 ^ a ≤ K * c) :
    (2 : NNReal) ^ a ≤ (K : NNReal) * (c : NNReal) := by
  exact_mod_cast h

/-- **J1 at the tube level.**  From an exact Definition-2.1 datum on `s` (only its cover, node
injectivity and bounded overlap are read) and a loose cover on `s` with node injectivity and the
anchored bounded overlap, one subfamily `s' ⊆ s` of polylogarithmic retention carries **both**
Definition-2.1 data, at the constant `twoTowerConst N L` joined to each datum's own overlap
constant. -/
theorem exists_joint_uniform_subfamily {δ : NNReal} {N : ℕ} {s : Finset ι} {T : ι → Tube δ E3}
    (hs : s.Nonempty) {C₁ : NNReal} (𝒰 : Tube.UniformTubeSet s T N C₁)
    (Lc : LooseGridCoverSystem s T N 4)
    (hLinj : ∀ k ≤ N, Set.InjOn (Lc.tube k) (Lc.indexSet k : Set ι))
    (hLbo : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E3,
      (open scoped Classical in
        ((Lc.indexSet k).filter (fun j => ∃ i ∈ s, Lc.assign k i = j ∧
          (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card)
        ≤ anchorOverlapConst)
    {L : ℕ} (hL : Nat.log 2 s.card ≤ L) :
    ∃ s' ⊆ s, s'.Nonempty ∧
      (s.card : ℝ) ≤ 2 * (L + 1 : ℝ) ^ (2 * (N + 1)) * (s'.card : ℝ) ∧
      Nonempty (Tube.UniformTubeSet s' T N (max C₁ (twoTowerConst N L : NNReal))) ∧
      Nonempty (LooseUniformTubeSet s' T N 4
        (max (twoTowerConst N L : NNReal) (anchorOverlapConst : NNReal))) := by
  classical
  obtain ⟨G, ae, al, hGs, hGne, hcard, -, hbe, hbl⟩ :=
    exists_two_tower_regular 𝒰.cover.assign Lc.assign N s hs hL
  have hK2 : 2 ≤ twoTowerConst N L := two_le_twoTowerConst N L
  have hKle₁ : (twoTowerConst N L : NNReal) ≤ max C₁ (twoTowerConst N L : NNReal) :=
    le_max_right _ _
  -- the exact restriction
  have himgE : ∀ k ≤ N, G.image (𝒰.cover.assign k) ⊆ 𝒰.cover.indexSet k := by
    intro k hk j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact 𝒰.cover.assign_mem k hk i (hGs hi)
  have himgL : ∀ k ≤ N, G.image (Lc.assign k) ⊆ Lc.indexSet k := by
    intro k hk j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Lc.assign_mem k hk i (hGs hi)
  refine ⟨G, hGs, hGne, hcard, ⟨?_⟩, ⟨?_⟩⟩
  · exact
      { cover :=
          { indexSet := fun k => G.image (𝒰.cover.assign k)
            assign := 𝒰.cover.assign
            tube := 𝒰.cover.tube
            assign_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
            le_tube_assign := fun k hk i hi => 𝒰.cover.le_tube_assign k hk i (hGs hi)
            nested := fun k hk i hi j hj h => 𝒰.cover.nested k hk i (hGs hi) j (hGs hj) h
            tube_nested := fun k hk i hi => 𝒰.cover.tube_nested k hk i (hGs hi) }
        branchingN := fun k => (2 : NNReal) ^ ae k
        tube_injOn := fun k hk =>
          Set.InjOn.mono (Finset.coe_subset.mpr (himgE k hk)) (𝒰.tube_injOn k hk)
        boundedOverlap := by
          intro k hk V
          refine le_trans ?_ (le_trans (𝒰.boundedOverlap k hk V) (le_max_left _ _))
          refine Nat.cast_le.mpr (Finset.card_le_card ?_)
          intro v hv
          rw [Finset.mem_filter] at hv ⊢
          obtain ⟨hv1, i, hi, h⟩ := hv
          exact ⟨himgE k hk hv1, i, hGs hi, h⟩
        card_class_le := by
          intro k hk j hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          refine le_trans (band_upper_nnreal hK2 (hbe k hk i hi).2) ?_
          exact mul_le_mul_of_nonneg_right hKle₁ (by positivity)
        le_card_class := by
          intro k hk j hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          refine le_trans (band_lower_nnreal (hbe k hk i hi).1) ?_
          exact mul_le_mul_of_nonneg_right hKle₁ (by positivity) }
  · refine LooseUniformTubeSet.ofCoverBrackets (s := G) (T := T)
      ({ indexSet := fun k => G.image (Lc.assign k)
         assign := Lc.assign
         tube := Lc.tube
         assign_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
         le_dilate_tube_assign := fun k hk i hi => Lc.le_dilate_tube_assign k hk i (hGs hi)
         dir_close_tube_assign := fun k hk i hi => Lc.dir_close_tube_assign k hk i (hGs hi)
         nested := fun k hk i hi j hj h => Lc.nested k hk i (hGs hi) j (hGs hj) h })
      (fun k => (2 : NNReal) ^ al k) (C := (twoTowerConst N L : NNReal)) ?_ ?_ ?_ ?_
    · intro k hk
      exact Set.InjOn.mono (Finset.coe_subset.mpr (himgL k hk)) (hLinj k hk)
    · intro k hk V
      refine le_trans (Finset.card_le_card ?_) (hLbo k hk V)
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      obtain ⟨hv1, i, hi, hij, hiV⟩ := hv
      exact ⟨himgL k hk hv1, i, hGs hi, hij, hiV⟩
    · intro k hk j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact band_upper_nnreal hK2 (hbl k hk i hi).2
    · intro k hk j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact band_lower_nnreal (hbl k hk i hi).1

end TubeLevel


/-! ### J1 at the shade level: GWZ Definition 2.2 for both towers at once -/

section ShadeLevel

open MeasureTheory Kakeya.LooseUniform

/-- The shade-fibre at `x`: the members of `s` whose shade contains `x`. -/
noncomputable def sFiber {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3) (x : E3) :
    Finset ι :=
  open scoped Classical in s.filter (fun i => x ∈ (V i).shade)

theorem mem_sFiber {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E3} {x : E3} {i : ι} :
    i ∈ sFiber s V x ↔ i ∈ s ∧ x ∈ (V i).shade := by
  classical
  simp [sFiber]

theorem sFiber_subset {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3) (x : E3) :
    sFiber s V x ⊆ s := fun _ hi => (mem_sFiber.mp hi).1

theorem measurableSet_sFiber_eq {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (S : Finset ι) : MeasurableSet {x : E3 | sFiber s V x = S} := by
  classical
  by_cases hS : S ⊆ s
  · have hset : {x : E3 | sFiber s V x = S}
        = (⋂ i ∈ S, (V i).shade) ∩ (⋂ i ∈ (s \ S), (V i).shadeᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Finset.mem_sdiff]
      constructor
      · intro hx
        refine ⟨fun i hiS => ?_, fun i hi hxi => ?_⟩
        · exact (mem_sFiber.mp (hx ▸ hiS)).2
        · exact hi.2 (hx ▸ mem_sFiber.mpr ⟨hi.1, hxi⟩)
      · rintro ⟨h1, h2⟩
        ext i
        rw [mem_sFiber]
        constructor
        · rintro ⟨hit, hxi⟩
          by_contra hiS
          exact h2 i ⟨hit, hiS⟩ hxi
        · intro hiS
          exact ⟨hS hiS, h1 i hiS⟩
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.biInter S.countable_toSet (fun i _ => (V i).measurableSet_shade))
      (MeasurableSet.biInter (s \ S).countable_toSet
        (fun i _ => (V i).measurableSet_shade.compl))
  · have hempty : {x : E3 | sFiber s V x = S} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hS (hx ▸ sFiber_subset s V x)
    rw [hempty]; exact MeasurableSet.empty

theorem measurableSet_profile_eq {δ : NNReal} {β : Type*} (s : Finset ι)
    (V : ι → ShadedTube δ E3) (bN : Finset ι → β) (p : β) :
    MeasurableSet {x : E3 | bN (sFiber s V x) = p} := by
  classical
  have hset : {x : E3 | bN (sFiber s V x) = p}
      = ⋃ S ∈ s.powerset.filter (fun S => bN S = p), {x : E3 | sFiber s V x = S} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro hx
      exact ⟨sFiber s V x, ⟨sFiber_subset s V x, hx⟩, rfl⟩
    · rintro ⟨S, ⟨_, hSp⟩, hxS⟩
      rw [hxS]; exact hSp
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_sFiber_eq s V S)

/-- **Profile pigeonhole on the shade sum.** -/
theorem exists_dominant_profile_sum {δ : NNReal} {β : Type*} [DecidableEq β] (s : Finset ι)
    (V : ι → ShadedTube δ E3) (bN : Finset ι → β)
    (A : ι → Set E3) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ p : β, p ∈ s.powerset.image bN ∧
      ∑ i ∈ s, volume (A i)
        ≤ (s.powerset.image bN).card
          • ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p}) := by
  classical
  set Tp := s.powerset.image bN with hTp
  have hTne : Tp.Nonempty :=
    ⟨bN ∅, Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset _, rfl⟩⟩
  have hpart : ∀ i, volume (A i)
      = ∑ p ∈ Tp, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p}) := by
    intro i
    have hd : (↑Tp : Set β).PairwiseDisjoint
        (fun p => A i ∩ {x : E3 | bN (sFiber s V x) = p}) := by
      intro p _ q _ hpq
      apply Set.disjoint_left.mpr
      intro x hxp hxq
      exact hpq (hxp.2.symm.trans hxq.2)
    have hm : ∀ p ∈ Tp, MeasurableSet (A i ∩ {x : E3 | bN (sFiber s V x) = p}) :=
      fun p _ => (hA i).inter (measurableSet_profile_eq s V bN p)
    have hcover : A i = ⋃ p ∈ Tp, A i ∩ {x : E3 | bN (sFiber s V x) = p} := by
      ext x
      simp only [Set.mem_iUnion₂, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hx
        exact ⟨bN (sFiber s V x),
          Finset.mem_image.mpr ⟨sFiber s V x,
            Finset.mem_powerset.mpr (sFiber_subset s V x), rfl⟩, hx, rfl⟩
      · rintro ⟨p, _, hx, _⟩; exact hx
    conv_lhs => rw [hcover]
    exact MeasureTheory.measure_biUnion_finset hd hm
  have hsum : ∑ i ∈ s, volume (A i)
      = ∑ p ∈ Tp, ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p}) := by
    simp_rw [hpart]
    rw [Finset.sum_comm]
  obtain ⟨p, hp, hmax⟩ := Tp.exists_max_image
    (fun p => ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p})) hTne
  refine ⟨p, hp, ?_⟩
  rw [hsum]
  calc ∑ q ∈ Tp, ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = q})
      ≤ ∑ _q ∈ Tp, ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p}) :=
        Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = Tp.card • ∑ i ∈ s, volume (A i ∩ {x : E3 | bN (sFiber s V x) = p}) := by
        rw [Finset.sum_const]

/-- The refined shade: keep `x ∈ Y(i)` only when `i` survives in the pruned fibre `g (F_x)`,
and only on the point-cell `X`. -/
noncomputable def rShade {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (g : Finset ι → Finset ι) (X : Set E3) (i : ι) : Set E3 :=
  ((V i).shade ∩ {x : E3 | i ∈ g (sFiber s V x)}) ∩ X

theorem rShade_subset {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (g : Finset ι → Finset ι) (X : Set E3) (i : ι) : rShade s V g X i ⊆ (V i).shade :=
  Set.inter_subset_left.trans Set.inter_subset_left

theorem measurableSet_rShade {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (g : Finset ι → Finset ι) {X : Set E3} (hX : MeasurableSet X) (i : ι) :
    MeasurableSet (rShade s V g X i) := by
  classical
  have hset : {x : E3 | i ∈ g (sFiber s V x)}
      = ⋃ S ∈ (s.powerset.filter (fun S => i ∈ g S)), {x : E3 | sFiber s V x = S} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro hx
      exact ⟨sFiber s V x, ⟨sFiber_subset s V x, hx⟩, rfl⟩
    · rintro ⟨S, ⟨_, hiS⟩, hxS⟩
      rw [hxS]; exact hiS
  refine ((V i).measurableSet_shade.inter ?_).inter hX
  rw [hset]
  exact Finset.measurableSet_biUnion _ (fun S _ => measurableSet_sFiber_eq s V S)

theorem rShade_inter {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (g : Finset ι → Finset ι) (X : Set E3) (i : ι) :
    rShade s V g Set.univ i ∩ X = rShade s V g X i := by
  simp [rShade]

open scoped Classical in
/-- On the cell `X`, the `rShade`-fibre at `x` is exactly the pruned fibre `g (F_x)`. -/
theorem rShade_fiber {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (g : Finset ι → Finset ι) (hg : ∀ F, g F ⊆ F) (X : Set E3) {x : E3} (hxX : x ∈ X) :
    (s.filter (fun i => x ∈ rShade s V g X i)) = g (sFiber s V x) := by
  ext i
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, hx⟩
    exact hx.1.2
  · intro hig
    have hiF := mem_sFiber.mp (hg _ hig)
    exact ⟨hiF.1, ⟨⟨hiF.2, hig⟩, hxX⟩⟩

/-- The shade class of a node at a point of the cell is the class of that node inside the
pruned fibre. -/
theorem shadeClass_rShade_eq {δ : NNReal} {s : Finset ι} {V V' : ι → ShadedTube δ E3}
    (g : Finset ι → Finset ι) (hg : ∀ F, g F ⊆ F) (X : Set E3)
    (hV' : ∀ i, (V' i).shade = rShade s V g X i)
    (assign : ι → ι) (j : ι) {x : E3} (hxX : x ∈ X) :
    ShadedTube.shadeClass s V' assign j x = Tube.coverClass (g (sFiber s V x)) assign j := by
  classical
  ext i
  unfold ShadedTube.shadeClass
  constructor
  · intro hi
    have h1 := Finset.mem_filter.mp hi
    have hij := (mem_coverClass_iff s assign j i).mp h1.1
    have hx : x ∈ rShade s V g X i := (hV' i) ▸ h1.2
    exact (mem_coverClass_iff _ assign j i).mpr ⟨hx.1.2, hij.2⟩
  · intro hi
    have hij := (mem_coverClass_iff _ assign j i).mp hi
    have hiF := mem_sFiber.mp (hg _ hij.1)
    refine Finset.mem_filter.mpr ⟨(mem_coverClass_iff s assign j i).mpr ⟨hiF.1, hij.2⟩, ?_⟩
    rw [hV' i]
    exact ⟨⟨hiF.2, hij.1⟩, hxX⟩

open scoped Classical in
/-- The multiplicity-integral step: a pointwise fibre bound integrates to a shade-sum bound. -/
theorem sum_le_of_fiber_card_le (R : ℕ) (s : Finset ι) (sh Yr : ι → Set E3)
    (hsh : ∀ i, MeasurableSet (sh i)) (hYr : ∀ i, MeasurableSet (Yr i))
    (hcard : ∀ x : E3, (s.filter (fun i => x ∈ sh i)).card
        ≤ R * (s.filter (fun i => x ∈ Yr i)).card) :
    ∑ i ∈ s, volume (sh i) ≤ (R : ENNReal) * ∑ i ∈ s, volume (Yr i) := by
  rw [MeasureTheory.sum_volume_eq_lintegral_card s sh hsh,
    MeasureTheory.sum_volume_eq_lintegral_card s Yr hYr,
    ← MeasureTheory.lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  apply MeasureTheory.lintegral_mono
  intro x
  have h := hcard x
  calc ((s.filter (fun i => x ∈ sh i)).card : ENNReal)
      ≤ ((R * (s.filter (fun i => x ∈ Yr i)).card : ℕ) : ENNReal) := by exact_mod_cast h
    _ = (R : ENNReal) * ((s.filter (fun i => x ∈ Yr i)).card : ENNReal) := by push_cast; ring

/-- **Stage 1 of the joint shade refinement: every fibre balanced for both towers.**  A choice of
`exists_two_tower_regular` on every sub-fibre, packaged as the pruning map `g`. -/
theorem exists_two_tower_fibre_balancer (ea la : ℕ → ι → ι) (M : ℕ) (s : Finset ι) {L : ℕ}
    (hL : Nat.log 2 s.card ≤ L) :
    ∃ (g : Finset ι → Finset ι) (be bl : Finset ι → ℕ → ℕ),
      (∀ F, g F ⊆ F) ∧
      (∀ F, F ⊆ s → F.Nonempty → (g F).Nonempty) ∧
      (∀ F, F ⊆ s → F.card ≤ 2 * (L + 1) ^ (2 * (M + 1)) * (g F).card) ∧
      (∀ F, F ⊆ s → ∀ k ≤ M, be F k ≤ L ∧ bl F k ≤ L) ∧
      (∀ F, F ⊆ s → ∀ k ≤ M, ∀ i ∈ g F,
        2 ^ be F k ≤ twoTowerConst M L * (Tube.coverClass (g F) (ea k) (ea k i)).card ∧
        (Tube.coverClass (g F) (ea k) (ea k i)).card < 2 ^ (be F k + 1)) ∧
      (∀ F, F ⊆ s → ∀ k ≤ M, ∀ i ∈ g F,
        2 ^ bl F k ≤ twoTowerConst M L * (Tube.coverClass (g F) (la k) (la k i)).card ∧
        (Tube.coverClass (g F) (la k) (la k i)).card < 2 ^ (bl F k + 1)) := by
  classical
  have key : ∀ F : Finset ι, ∃ q : Finset ι × ((ℕ → ℕ) × (ℕ → ℕ)),
      q.1 ⊆ F ∧
      (F ⊆ s → F.Nonempty → q.1.Nonempty) ∧
      (F ⊆ s → F.card ≤ 2 * (L + 1) ^ (2 * (M + 1)) * q.1.card) ∧
      (F ⊆ s → ∀ k ≤ M, q.2.1 k ≤ L ∧ q.2.2 k ≤ L) ∧
      (F ⊆ s → ∀ k ≤ M, ∀ i ∈ q.1,
        2 ^ q.2.1 k ≤ twoTowerConst M L * (Tube.coverClass q.1 (ea k) (ea k i)).card ∧
        (Tube.coverClass q.1 (ea k) (ea k i)).card < 2 ^ (q.2.1 k + 1)) ∧
      (F ⊆ s → ∀ k ≤ M, ∀ i ∈ q.1,
        2 ^ q.2.2 k ≤ twoTowerConst M L * (Tube.coverClass q.1 (la k) (la k i)).card ∧
        (Tube.coverClass q.1 (la k) (la k i)).card < 2 ^ (q.2.2 k + 1)) := by
    intro F
    by_cases hF : F ⊆ s ∧ F.Nonempty
    · have hLF : Nat.log 2 F.card ≤ L :=
        (Nat.log_mono_right (Finset.card_le_card hF.1)).trans hL
      obtain ⟨G, ae, al, hGF, hGne, hcard, haL, hbe, hbl⟩ :=
        exists_two_tower_regular ea la M F hF.2 hLF
      refine ⟨(G, (ae, al)), hGF, fun _ _ => hGne, fun _ => ?_, fun _ => haL, fun _ => hbe,
        fun _ => hbl⟩
      exact_mod_cast hcard
    · refine ⟨(∅, (fun _ => 0, fun _ => 0)), by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro hFs hFne; exact absurd ⟨hFs, hFne⟩ hF
      · intro hFs
        have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          (by intro hne; exact hF ⟨hFs, hne⟩)
        simp [hFempty]
      · intro _ k _; simp
      · intro _ k _ i hi; simp at hi
      · intro _ k _ i hi; simp at hi
  choose q hq using key
  exact ⟨fun F => (q F).1, fun F => (q F).2.1, fun F => (q F).2.2,
    fun F => (hq F).1, fun F hFs hFne => (hq F).2.1 hFs hFne, fun F hFs => (hq F).2.2.1 hFs,
    fun F hFs => (hq F).2.2.2.1 hFs, fun F hFs => (hq F).2.2.2.2.1 hFs,
    fun F hFs => (hq F).2.2.2.2.2 hFs⟩

/-- The two-tower profile vectors range over a cube of size `((L+1)^2)^{M+1}`. -/
theorem card_image_twoProfile_le {M L : ℕ} (be bl : Finset ι → ℕ → ℕ) (s : Finset ι)
    (hbound : ∀ F, F ⊆ s → ∀ k ≤ M, be F k ≤ L ∧ bl F k ≤ L) :
    (s.powerset.image
        (fun F : Finset ι => fun k : Fin (M + 1) => (be F k, bl F k))).card
      ≤ (L + 1) ^ (2 * (M + 1)) := by
  classical
  let Tp : Finset (Fin (M + 1) → ℕ × ℕ) :=
    Fintype.piFinset (fun _ : Fin (M + 1) => Finset.range (L + 1) ×ˢ Finset.range (L + 1))
  have hTcard : Tp.card = (L + 1) ^ (2 * (M + 1)) := by
    dsimp [Tp]
    rw [Fintype.card_piFinset]
    simp only [Finset.card_product, Finset.card_range]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_two, ← pow_mul, mul_comm]
  have himg : s.powerset.image
      (fun F : Finset ι => fun k : Fin (M + 1) => (be F k, bl F k)) ⊆ Tp := by
    intro v hv
    dsimp [Tp]
    rw [Fintype.mem_piFinset]
    intro k
    rcases Finset.mem_image.mp hv with ⟨F, hF, rfl⟩
    have hFs : F ⊆ s := Finset.mem_powerset.mp hF
    have hk : (k : ℕ) ≤ M := Nat.lt_succ_iff.mp k.isLt
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hbound F hFs k hk).1, Nat.lt_succ_of_le (hbound F hFs k hk).2⟩
  exact (Finset.card_le_card himg).trans hTcard.le

/-- **J1 at the shade level.**  A refinement of the shading — tubes unchanged, shades shrunk —
on which, at every retained point and grid index, the shade classes of **both** towers are
banded, with a single band vector for each tower across all points.  The shade-mass loss is
`2 (L+1)^{4(M+1)}`: one two-tower regularisation per fibre, one profile pigeonhole. -/
theorem exists_joint_shadeRefinement {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3)
    (ea la : ℕ → ι → ι) (M : ℕ) {L : ℕ} (hL : Nat.log 2 s.card ≤ L) :
    ∃ (Pe Pl : ℕ → ℕ) (V' : ι → ShadedTube δ E3),
      (∀ i, (V' i).toTube = (V i).toTube) ∧
      (∀ i, (V' i).shade ⊆ (V i).shade) ∧
      (∀ x ∈ (⋃ i ∈ s, (V' i).shade), ∀ k ≤ M, ∀ i ∈ s, x ∈ (V' i).shade →
        2 ^ Pe k ≤ twoTowerConst M L * (ShadedTube.shadeClass s V' (ea k) (ea k i) x).card ∧
          (ShadedTube.shadeClass s V' (ea k) (ea k i) x).card < 2 ^ (Pe k + 1)) ∧
      (∀ x ∈ (⋃ i ∈ s, (V' i).shade), ∀ k ≤ M, ∀ i ∈ s, x ∈ (V' i).shade →
        2 ^ Pl k ≤ twoTowerConst M L * (ShadedTube.shadeClass s V' (la k) (la k i) x).card ∧
          (ShadedTube.shadeClass s V' (la k) (la k i) x).card < 2 ^ (Pl k + 1)) ∧
      ∑ i ∈ s, volume (V i).shade
        ≤ ((2 * (L + 1) ^ (4 * (M + 1)) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
  classical
  obtain ⟨g, be, bl, hg_sub, _hg_ne, hg_card, hg_bound, hg_be, hg_bl⟩ :=
    exists_two_tower_fibre_balancer ea la M s hL
  set bN : Finset ι → (Fin (M + 1) → ℕ × ℕ) := fun F k => (be F k, bl F k) with hbN
  obtain ⟨Pfin, _hPmem, hPig⟩ :=
    exists_dominant_profile_sum s V bN (rShade s V g Set.univ)
      (measurableSet_rShade s V g MeasurableSet.univ)
  set Xstar : Set E3 := {x : E3 | bN (sFiber s V x) = Pfin} with hXstar
  have hXstar_meas : MeasurableSet Xstar := measurableSet_profile_eq s V bN Pfin
  set V' : ι → ShadedTube δ E3 := fun i =>
    { V i with
      shade := rShade s V g Xstar i
      measurableSet_shade := measurableSet_rShade s V g hXstar_meas i
      shade_subset := (rShade_subset s V g Xstar i).trans (V i).shade_subset } with hV'
  have hVto : ∀ i, (V' i).toTube = (V i).toTube := fun i => rfl
  have hVshade : ∀ i, (V' i).shade = rShade s V g Xstar i := fun i => rfl
  have hVsub : ∀ i, (V' i).shade ⊆ (V i).shade := fun i => rShade_subset s V g Xstar i
  set Pe : ℕ → ℕ := fun k => if h : k < M + 1 then (Pfin ⟨k, h⟩).1 else 0 with hPe
  set Pl : ℕ → ℕ := fun k => if h : k < M + 1 then (Pfin ⟨k, h⟩).2 else 0 with hPl
  -- the band, from a point of the cell
  have hpoint : ∀ x, ∀ k ≤ M, ∀ i ∈ s, x ∈ (V' i).shade →
      x ∈ Xstar ∧ i ∈ g (sFiber s V x) ∧ be (sFiber s V x) k = Pe k ∧
        bl (sFiber s V x) k = Pl k := by
    intro x k hk i _ hxi
    rw [hVshade i] at hxi
    have hxX : x ∈ Xstar := hxi.2
    have hig : i ∈ g (sFiber s V x) := hxi.1.2
    have hk' : k < M + 1 := Nat.lt_succ_of_le hk
    have hxXeq : bN (sFiber s V x) = Pfin := hxX
    refine ⟨hxX, hig, ?_, ?_⟩
    · simp only [hPe, dif_pos hk']
      rw [← hxXeq]
    · simp only [hPl, dif_pos hk']
      rw [← hxXeq]
  refine ⟨Pe, Pl, V', hVto, hVsub, ?_, ?_, ?_⟩
  · intro x _ k hk i hi hxi
    obtain ⟨hxX, hig, hbe, -⟩ := hpoint x k hk i hi hxi
    rw [shadeClass_rShade_eq g hg_sub Xstar hVshade (ea k) (ea k i) hxX, ← hbe]
    exact hg_be _ (sFiber_subset s V x) k hk i hig
  · intro x _ k hk i hi hxi
    obtain ⟨hxX, hig, -, hbl⟩ := hpoint x k hk i hi hxi
    rw [shadeClass_rShade_eq g hg_sub Xstar hVshade (la k) (la k i) hxX, ← hbl]
    exact hg_bl _ (sFiber_subset s V x) k hk i hig
  · -- stage 1
    have hcard_pt : ∀ x : E3, (s.filter (fun i => x ∈ (V i).shade)).card
        ≤ 2 * (L + 1) ^ (2 * (M + 1))
          * (s.filter (fun i => x ∈ rShade s V g Set.univ i)).card := by
      intro x
      rw [rShade_fiber s V g hg_sub Set.univ (Set.mem_univ x)]
      exact hg_card _ (sFiber_subset s V x)
    have hstage1 : ∑ i ∈ s, volume (V i).shade
        ≤ ((2 * (L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal)
          * ∑ i ∈ s, volume (rShade s V g Set.univ i) :=
      sum_le_of_fiber_card_le _ s (fun i => (V i).shade) (rShade s V g Set.univ)
        (fun i => (V i).measurableSet_shade) (measurableSet_rShade s V g MeasurableSet.univ)
        hcard_pt
    -- stage 2
    have himg : ((s.powerset.image bN).card : ENNReal)
        ≤ (((L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal) := by
      exact_mod_cast card_image_twoProfile_le be bl s hg_bound
    have hstage2 : ∑ i ∈ s, volume (rShade s V g Set.univ i)
        ≤ (((L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
      calc ∑ i ∈ s, volume (rShade s V g Set.univ i)
          ≤ (s.powerset.image bN).card
              • ∑ i ∈ s, volume (rShade s V g Set.univ i ∩ Xstar) := hPig
        _ = ((s.powerset.image bN).card : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
            rw [nsmul_eq_mul]
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hVshade i, rShade_inter]
        _ ≤ (((L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
            gcongr
    calc ∑ i ∈ s, volume (V i).shade
        ≤ ((2 * (L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal)
            * ∑ i ∈ s, volume (rShade s V g Set.univ i) := hstage1
      _ ≤ ((2 * (L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal)
            * ((((L + 1) ^ (2 * (M + 1)) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade) := by
          gcongr
      _ = ((2 * (L + 1) ^ (4 * (M + 1)) : ℕ) : ENNReal) * ∑ i ∈ s, volume (V' i).shade := by
          rw [← mul_assoc]
          congr 1
          push_cast
          rw [mul_assoc, ← pow_add]
          congr 2
          ring

end ShadeLevel


/-! ### Transport along equal tubes -/

section Retube

open Kakeya.LooseUniform

/-- Re-typing an exact Definition-2.1 datum over a pointwise-equal tube family.  All data
(index sets, assignments, nodes, branching numbers) are unchanged, so the projections are
`rfl`. -/
def retubeUniform {δ : NNReal} {N : ℕ} {C : NNReal} {s : Finset ι} {T T' : ι → Tube δ E3}
    (h : ∀ i, T' i = T i) (𝒰 : Tube.UniformTubeSet s T N C) : Tube.UniformTubeSet s T' N C where
  cover :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_tube_assign := fun k hk i hi => by rw [h i]; exact 𝒰.cover.le_tube_assign k hk i hi
      nested := 𝒰.cover.nested
      tube_nested := 𝒰.cover.tube_nested }
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlap := by
    intro k hk V
    have hT : T' = T := funext h
    subst hT
    exact 𝒰.boundedOverlap k hk V
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

/-- Re-typing a loose Definition-2.1 datum over a pointwise-equal tube family. -/
def retubeLoose {δ : NNReal} {N : ℕ} {K : ℝ} {C : NNReal} {s : Finset ι}
    {T T' : ι → Tube δ E3} (h : ∀ i, T' i = T i) (𝒰 : LooseUniformTubeSet s T N K C) :
    LooseUniformTubeSet s T' N K C where
  cover :=
    { indexSet := 𝒰.cover.indexSet
      assign := 𝒰.cover.assign
      tube := 𝒰.cover.tube
      assign_mem := 𝒰.cover.assign_mem
      le_dilate_tube_assign := fun k hk i hi => by
        rw [h i]; exact 𝒰.cover.le_dilate_tube_assign k hk i hi
      dir_close_tube_assign := fun k hk i hi => by
        rw [h i]; exact 𝒰.cover.dir_close_tube_assign k hk i hi
      nested := 𝒰.cover.nested }
  branchingN := 𝒰.branchingN
  tube_injOn := 𝒰.tube_injOn
  boundedOverlapDil := by
    intro k hk V
    have hT : T' = T := funext h
    subst hT
    exact 𝒰.boundedOverlapDil k hk V
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

end Retube

/-! ### The joint refinement at GWZ's grid length -/

section Assembly

open Kakeya.LooseUniform

/-- The anchored loose cover on any family in `B₁`, from the grid separation `δ ≤ 16^{-N}`
(the two grid hypotheses of `exists_looseGridCover`, discharged as in
`exists_looseUniformTubeSet_subfamily`). -/
theorem exists_looseGridCover_of_sep {δ : NNReal} (N : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : 0 < N) (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (s : Finset ι) (T : ι → Tube δ E3)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) :
    ∃ cover : LooseGridCoverSystem s T N 4,
      (∀ k, k ≤ N → Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)) ∧
      (∀ k, k ≤ N → ∀ V : Tube (Tube.gridScale δ N k) E3,
        (open scoped Classical in
          ((cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
            (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V ((4 : ℝ) + 4))).card)
          ≤ anchorOverlapConst) := by
  classical
  have hδnonneg : (0 : ℝ) ≤ (δ : ℝ) := (δ : NNReal).coe_nonneg
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hgap : (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 / 2 := by
    have hδle16R : (δ : ℝ) ≤ (16 : ℝ) ^ (-(N : ℝ)) := by
      have hcast : (δ : ℝ) ≤ (((16 : NNReal) ^ (-(N : ℝ)) : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr hδ0
      simpa [NNReal.coe_rpow] using hcast
    have hprod : (-(N : ℝ)) * ((1 : ℝ) / (N : ℝ)) = -1 := by field_simp
    calc (δ : ℝ) ^ ((1 : ℝ) / (N : ℝ)) ≤ ((16 : ℝ) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) :=
          Real.rpow_le_rpow hδnonneg hδle16R (by positivity)
      _ = (1 : ℝ) / 16 := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16), hprod]; norm_num
      _ ≤ 1 / 2 := by norm_num
  have hgapρ : ∀ k, 2 * ((Tube.gridScale δ N (k + 1) : NNReal) : ℝ)
      ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    intro k
    have h := Tube.rho_scale_gap hδ hN hgap k
    simpa [Tube.gridScale, NNReal.coe_rpow] using h
  have hδle : ∀ k, k ≤ N → (δ : ℝ) ≤ ((Tube.gridScale δ N k : NNReal) : ℝ) := by
    intro k hk
    have h1 := Tube.gridScale_antitone hδ hδ1 N hk
    rw [Tube.gridScale_self δ hN] at h1
    exact_mod_cast h1
  obtain ⟨cover, hinj, hbo, -⟩ := exists_looseGridCover hδ hδ1 s T hB hgapρ hδle
  exact ⟨cover, hinj, hbo⟩

/-- The common constant of the joint refinement. -/
noncomputable def jointConst (C₀ Cj : NNReal) : NNReal :=
  max (max C₀ (anchorOverlapConst : NNReal)) Cj

theorem le_jointConst_left (C₀ Cj : NNReal) : C₀ ≤ jointConst C₀ Cj :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem anchorOverlapConst_le_jointConst (C₀ Cj : NNReal) :
    (anchorOverlapConst : NNReal) ≤ jointConst C₀ Cj :=
  (le_max_right _ _).trans (le_max_left _ _)

theorem le_jointConst_right (C₀ Cj : NNReal) : Cj ≤ jointConst C₀ Cj := le_max_right _ _

/-- **J1 — `exists_joint_refinement`.**  Every family `(s, V)` of `δ`-tubes in `B₁` with
`|s| ≤ δ^{-K₀}` carrying an exact GWZ Definition-2.2 datum at the grid length
`Tube.ssfGridLen δ` has a refinement `(s', V')` — index subset, tubes unchanged, shades shrunk,
cardinality retained up to `δ^{-α}`, fullness retained up to `δ^{-α'}` — carrying **both** the
exact Definition-2.2 datum and the loose one (`LooseShadedUniformTubeSet`, dilation `4`) at one
common constant `jointConst C₀ Cj`, where `Cj ≤ δ^{-α}` is the two-tower regularisation
constant.  The two data live on the **same** family `s'`, which is what conjunct 6 of
`SideDataObligations` and the configuration's own `uniform` field jointly demand. -/
theorem exists_joint_refinement (K₀ : ℕ) (α α' : ℝ) (hα : 0 < α) (hα' : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (s : Finset ι) (V : ι → ShadedTube δ E3) {C₀ : NNReal},
      s.Nonempty →
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E3) 1) →
      (s.card : ℝ) ≤ (δ : ℝ) ^ (-(K₀ : ℝ)) →
      Nonempty (ShadedTube.ShadedUniformTubeSet s V (Tube.ssfGridLen δ) C₀) →
      ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E3, ∃ Cj : NNReal,
        s'.Nonempty ∧
        (∀ i, (V' i).toTube = (V i).toTube) ∧
        (∀ i, (V' i).shade ⊆ (V i).shade) ∧
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
        ShadedBody.fullness' s' (fun i => (V i).toShadedBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α'))
              * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) ∧
        1 ≤ Cj ∧ (Cj : ℝ) ≤ (δ : ℝ) ^ (-α) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet s' V' (Tube.ssfGridLen δ) (jointConst C₀ Cj)) ∧
        Nonempty (LooseShadedUniformTubeSet s' V' (Tube.ssfGridLen δ) 4 (jointConst C₀ Cj)) := by
  classical
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, hthr₁⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 8 (by norm_num) K₀ 2 α hα
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, hthr₂⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 8 (by norm_num) K₀ 4 α' hα'
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le1, ?_⟩
  intro ι δ hδ hδ0 s V C₀ hs hB hcardK ⟨𝒱⟩
  have hδ1 : δ ≤ 1 := hδ0.trans ((min_le_left _ _).trans hδ₁le1)
  obtain ⟨hNpos, hδ16, hpoly₁⟩ := hthr₁ hδ (hδ0.trans (min_le_left _ _))
  obtain ⟨-, -, hpoly₂⟩ := hthr₂ hδ (hδ0.trans (min_le_right _ _))
  set N := Tube.ssfGridLen δ with hN
  set L := Nat.log 2 s.card with hL
  have hLfloor : (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) = (L : ℝ) := by
    rw [hL]; exact_mod_cast Real.natFloor_logb_natCast 2 s.card
  have hcard0 : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  have hpoly₁' : (8 * ((L : ℝ) + 1)) ^ (2 * N + 2) ≤ (δ : ℝ) ^ (-α) := by
    have := hpoly₁ (s.card : ℝ) hcard0 hcardK
    rwa [hLfloor, show 2 * N + 2 = 2 * N + 2 from rfl] at this
  have hpoly₂' : (8 * ((L : ℝ) + 1)) ^ (4 * N + 4) ≤ (δ : ℝ) ^ (-α') := by
    have := hpoly₂ (s.card : ℝ) hcard0 hcardK
    rwa [hLfloor] at this
  -- the loose cover on `s`
  have hBt : ∀ i ∈ s, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
    intro i hi; simpa using hB i hi
  obtain ⟨Lc, hLinj, hLbo⟩ :=
    exists_looseGridCover_of_sep N hδ hδ1 hNpos hδ16 s (fun i => (V i).toTube) hBt
  set Cj : NNReal := (twoTowerConst N L : NNReal) with hCj
  have hK2 : 2 ≤ twoTowerConst N L := two_le_twoTowerConst N L
  have hCj1 : (1 : NNReal) ≤ Cj := by
    rw [hCj]; exact_mod_cast (le_trans (by norm_num) hK2)
  have hCjR : (Cj : ℝ) ≤ (δ : ℝ) ^ (-α) := by
    rw [hCj, NNReal.coe_natCast]
    exact (twoTowerConst_le N L).trans hpoly₁'
  set C : NNReal := jointConst C₀ Cj with hC
  have hC2 : (2 : NNReal) ≤ C := by
    calc (2 : NNReal) ≤ Cj := by rw [hCj]; exact_mod_cast hK2
      _ ≤ C := le_jointConst_right _ _
  have hC1 : (1 : NNReal) ≤ C := le_trans (by norm_num) hC2
  have hCjC : Cj ≤ C := le_jointConst_right _ _
  have hE : max C₀ Cj ≤ C := max_le (le_jointConst_left _ _) hCjC
  have hLC : max Cj (anchorOverlapConst : NNReal) ≤ C :=
    max_le hCjC (anchorOverlapConst_le_jointConst _ _)
  -- the tube-level joint refinement
  obtain ⟨s', hs's, hs'ne, hcard', ⟨𝒰E⟩, ⟨𝒰L⟩⟩ :=
    exists_joint_uniform_subfamily hs 𝒱.tubeUniform Lc hLinj hLbo (le_refl L)
  -- the shade-level joint refinement on `s'`
  have hL' : Nat.log 2 s'.card ≤ L := Nat.log_mono_right (Finset.card_le_card hs's)
  obtain ⟨Pe, Pl, V', hVto, hVsub, hbandE, hbandL, hmass⟩ :=
    exists_joint_shadeRefinement s' V 𝒰E.cover.assign 𝒰L.cover.assign N hL'
  refine ⟨s', hs's, V', Cj, hs'ne, hVto, hVsub, ?_, ?_, hCj1, hCjR, ⟨?_⟩, ⟨?_⟩⟩
  · -- cardinality
    calc (s.card : ℝ) ≤ 2 * (L + 1 : ℝ) ^ (2 * (N + 1)) * (s'.card : ℝ) := hcard'
      _ ≤ (8 * ((L : ℝ) + 1)) ^ (2 * N + 2) * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right (two_mul_pow_le N L) (by positivity)
      _ ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_right hpoly₁' (by positivity)
  · -- fullness
    refine le_trans (fullness_le_of_shade_sum' _ V V' hVto hmass) ?_
    refine mul_le_mul' ?_ le_rfl
    have hreal : ((2 * (L + 1) ^ (4 * (N + 1)) : ℕ) : ℝ) ≤ (δ : ℝ) ^ (-α') := by
      refine le_trans ?_ hpoly₂'
      push_cast
      have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
      have h2 : (2 : ℝ) ≤ 8 ^ (4 * N + 4) := by
        calc (2 : ℝ) ≤ 8 := by norm_num
          _ = 8 ^ 1 := (pow_one _).symm
          _ ≤ 8 ^ (4 * N + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [mul_pow, show 4 * (N + 1) = 4 * N + 4 by ring]
      exact mul_le_mul_of_nonneg_right h2 (pow_nonneg hL0 _)
    calc ((2 * (L + 1) ^ (4 * (N + 1)) : ℕ) : ENNReal)
        = ENNReal.ofReal ((2 * (L + 1) ^ (4 * (N + 1)) : ℕ) : ℝ) := by
          rw [ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α')) := ENNReal.ofReal_le_ofReal hreal
  · -- the exact Definition-2.2 datum on `(s', V')`
    exact
      { tubeUniform := retubeUniform hVto (𝒰E.mono hE)
        branchingN := fun k => (2 : NNReal) ^ Pe k
        localN := fun _ k => (2 : NNReal) ^ Pe k
        card_shadeClass_le := by
          intro x hx k hk i hi hxi
          have hb := (hbandE x hx k hk i hi hxi).2
          exact le_trans (band_upper_nnreal (c := _) (K := twoTowerConst N L) hK2 hb)
            (mul_le_mul' hCjC le_rfl)
        le_card_shadeClass := by
          intro x hx k hk i hi hxi
          have hb := (hbandE x hx k hk i hi hxi).1
          exact le_trans (band_lower_nnreal hb) (mul_le_mul' hCjC le_rfl)
        branchingN_le := fun x _ k _ => le_mul_of_one_le_left (by positivity) hC1
        le_branchingN := fun x _ k _ => le_mul_of_one_le_left (by positivity) hC1 }
  · -- the loose Definition-2.2 datum on `(s', V')`
    exact
      { tubeUniform := retubeLoose hVto (𝒰L.mono hLC)
        branchingN := fun k => (2 : NNReal) ^ Pl k
        localN := fun _ k => (2 : NNReal) ^ Pl k
        card_shadeClass_le := by
          intro x hx k hk i hi hxi
          have hb := (hbandL x hx k hk i hi hxi).2
          exact le_trans (band_upper_nnreal (c := _) (K := twoTowerConst N L) hK2 hb)
            (mul_le_mul' hCjC le_rfl)
        le_card_shadeClass := by
          intro x hx k hk i hi hxi
          have hb := (hbandL x hx k hk i hi hxi).1
          exact le_trans (band_lower_nnreal hb) (mul_le_mul' hCjC le_rfl)
        branchingN_le := fun x _ k _ => le_mul_of_one_le_left (by positivity) hC1
        le_branchingN := fun x _ k _ => le_mul_of_one_le_left (by positivity) hC1 }

end Assembly

end Kakeya.JointRefine

end
