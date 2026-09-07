module

/-
  B1 Bridge — S-set transfer between main repo and standalone proof.

  Key insight: DyadicTubes in a Finset are automatically δ-separated
  (minimum L1 distance = dyadicDelta n for distinct tubes).
  This allows transferring between:
  - Main repo: IsDeltaSSet (metric covering number)
  - Standalone: IsFiniteTubeSSet (discrete Frostman + separation)

  Constant loss: O(1) factor from L1↔L∞ metric equivalence and packing.

  Whiteprint node: B1_induction_on_scales / SSet_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.InductionOnScales

open DiscretisedFurstenbergEstimate

/-! ============================================================================
   Metric equivalence: L1 (main repo dist) vs L∞ (standalone tubeParamDist)
   ============================================================================ -/

/-- L∞ parameter distance (standalone's tubeParamDist). -/
def tubeParamDistLinf {n : ℕ} (T U : DyadicTube n) : ℝ :=
  max |T.slope - U.slope| |T.intercept - U.intercept|

/-- L1 dist ≤ 2 * L∞ dist. -/
lemma dist_le_two_linf {n : ℕ} (T U : DyadicTube n) :
    T.dist U ≤ 2 * tubeParamDistLinf T U := by
  dsimp only [tubeParamDistLinf, DyadicTube.dist]
  have h1 : |T.slope - U.slope| ≤ max |T.slope - U.slope| |T.intercept - U.intercept| :=
    le_max_left _ _
  have h2 : |T.intercept - U.intercept| ≤ max |T.slope - U.slope| |T.intercept - U.intercept| :=
    le_max_right _ _
  linarith

/-- L∞ dist ≤ L1 dist. -/
lemma linf_le_dist {n : ℕ} (T U : DyadicTube n) :
    tubeParamDistLinf T U ≤ T.dist U := by
  dsimp only [tubeParamDistLinf, DyadicTube.dist]
  have ha : 0 ≤ |T.slope - U.slope| := abs_nonneg _
  have hb : 0 ≤ |T.intercept - U.intercept| := abs_nonneg _
  have h : max |T.slope - U.slope| |T.intercept - U.intercept| ≤
      |T.slope - U.slope| + |T.intercept - U.intercept| := by
    exact max_le (by linarith) (by linarith)
  exact h

/-! ============================================================================
   Packing bound: δ-separated dyadic tubes in a δ-ball
   ============================================================================ -/

/-- If integers da, db satisfy |da| + |db| ≤ 1, then (da, db) is one of
    (0,0), (±1,0), (0,±1). -/
lemma int_abs_sum_le_one (da db : ℤ) (h : |da| + |db| ≤ 1) :
    (da = 0 ∧ db = 0) ∨ (da = 1 ∧ db = 0) ∨ (da = -1 ∧ db = 0) ∨
    (da = 0 ∧ db = 1) ∨ (da = 0 ∧ db = -1) := by
  have h1 : |da| ≤ 1 := by linarith [abs_nonneg db]
  have h2 : |db| ≤ 1 := by linarith [abs_nonneg da]
  have hda1 : -1 ≤ da := by linarith [abs_le.mp h1]
  have hda2 : da ≤ 1 := by linarith [abs_le.mp h1]
  have hdb1 : -1 ≤ db := by linarith [abs_le.mp h2]
  have hdb2 : db ≤ 1 := by linarith [abs_le.mp h2]
  interval_cases da <;> interval_cases db <;> simp (config := {decide := true}) [abs_of_nonneg, abs_of_nonpos] at h ⊢ <;>
    (try { tauto }) <;> (try { omega })

/-- Any δ-ball in L1 metric contains at most 5 distinct DyadicTubes. -/
lemma ball_packing_bound {n : ℕ} (center : DyadicTube n) (F : Finset (DyadicTube n)) :
    (F.filter fun T => T.dist center ≤ dyadicDelta n).card ≤ 5 := by
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_main : ∀ T ∈ F, T.dist center ≤ dyadicDelta n →
      T = center ∨ T = { a := center.a + 1, b := center.b } ∨
      T = { a := center.a - 1, b := center.b } ∨
      T = { a := center.a, b := center.b + 1 } ∨
      T = { a := center.a, b := center.b - 1 } := by
    intro T _ hdist
    set da : ℤ := T.a - center.a with hda
    set db : ℤ := T.b - center.b with hdb
    have h1 : (|da| : ℝ) + (|db| : ℝ) ≤ 1 := by
      have h2 : T.dist center = dyadicDelta n * ((|da| : ℝ) + (|db| : ℝ)) :=
        DyadicTube.dist_eq T center
      rw [h2] at hdist
      nlinarith [hδ_pos]
    have h3 : |da| + |db| ≤ 1 := by exact_mod_cast h1
    have h4 := int_abs_sum_le_one da db h3
    rcases h4 with (h4 | h4 | h4 | h4 | h4)
    · have hda0 : da = 0 := h4.1
      have hdb0 : db = 0 := h4.2
      have ha : T.a = center.a := by omega
      have hb : T.b = center.b := by omega
      have hT : T = center := by
        cases T <;> cases center <;> simp_all
      exact Or.inl hT
    · have hda1 : da = 1 := h4.1
      have hdb0 : db = 0 := h4.2
      have ha : T.a = center.a + 1 := by omega
      have hb : T.b = center.b := by omega
      have hT : T = { a := center.a + 1, b := center.b } := by
        cases T <;> simp_all
      exact Or.inr (Or.inl hT)
    · have hda1 : da = -1 := h4.1
      have hdb0 : db = 0 := h4.2
      have ha : T.a = center.a - 1 := by omega
      have hb : T.b = center.b := by omega
      have hT : T = { a := center.a - 1, b := center.b } := by
        cases T <;> simp_all
      exact Or.inr (Or.inr (Or.inl hT))
    · have hda0 : da = 0 := h4.1
      have hdb1 : db = 1 := h4.2
      have ha : T.a = center.a := by omega
      have hb : T.b = center.b + 1 := by omega
      have hT : T = { a := center.a, b := center.b + 1 } := by
        cases T <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inl hT)))
    · have hda0 : da = 0 := h4.1
      have hdb1 : db = -1 := h4.2
      have ha : T.a = center.a := by omega
      have hb : T.b = center.b - 1 := by omega
      have hT : T = { a := center.a, b := center.b - 1 } := by
        cases T <;> simp_all
      exact Or.inr (Or.inr (Or.inr (Or.inr hT)))
  let candidates : Finset (DyadicTube n) :=
    {center, {a := center.a + 1, b := center.b}, {a := center.a - 1, b := center.b},
     {a := center.a, b := center.b + 1}, {a := center.a, b := center.b - 1}}
  have h_sub : (F.filter fun T => T.dist center ≤ dyadicDelta n) ⊆ candidates := by
    intro T hT
    have h4 : T.dist center ≤ dyadicDelta n := (Finset.mem_filter.mp hT).2
    have h5 := h_main T (Finset.mem_filter.mp hT).1 h4
    rcases h5 with (rfl | rfl | rfl | rfl | rfl) <;> simp [candidates] <;> tauto
  have h_ne1 : center ≠ ({a := center.a + 1, b := center.b} : DyadicTube n) := by
    intro h; have h' : center.a = center.a + 1 := congr_arg (fun (t : DyadicTube n) => t.a) h; linarith
  have h_ne2 : center ≠ ({a := center.a - 1, b := center.b} : DyadicTube n) := by
    intro h; have h' : center.a = center.a - 1 := congr_arg (fun (t : DyadicTube n) => t.a) h; linarith
  have h_ne3 : center ≠ ({a := center.a, b := center.b + 1} : DyadicTube n) := by
    intro h; have h' : center.b = center.b + 1 := congr_arg (fun (t : DyadicTube n) => t.b) h; linarith
  have h_ne4 : center ≠ ({a := center.a, b := center.b - 1} : DyadicTube n) := by
    intro h; have h' : center.b = center.b - 1 := congr_arg (fun (t : DyadicTube n) => t.b) h; linarith
  have h_ne5 : ({a := center.a + 1, b := center.b} : DyadicTube n) ≠
      ({a := center.a - 1, b := center.b} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_ne6 : ({a := center.a + 1, b := center.b} : DyadicTube n) ≠
      ({a := center.a, b := center.b + 1} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_ne7 : ({a := center.a + 1, b := center.b} : DyadicTube n) ≠
      ({a := center.a, b := center.b - 1} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_ne8 : ({a := center.a - 1, b := center.b} : DyadicTube n) ≠
      ({a := center.a, b := center.b + 1} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_ne9 : ({a := center.a - 1, b := center.b} : DyadicTube n) ≠
      ({a := center.a, b := center.b - 1} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_ne10 : ({a := center.a, b := center.b + 1} : DyadicTube n) ≠
      ({a := center.a, b := center.b - 1} : DyadicTube n) := by
    intro h; injection h <;> omega
  have h_card : candidates.card = 5 := by
    simp [candidates, Finset.mem_insert, Finset.mem_singleton,
      h_ne1, h_ne2, h_ne3, h_ne4, h_ne5, h_ne6, h_ne7, h_ne8, h_ne9, h_ne10]
    <;> rfl
  have h6 : (F.filter fun T => T.dist center ≤ dyadicDelta n).card ≤ candidates.card :=
    Finset.card_le_card h_sub
  rw [h_card] at h6
  exact h6

/-! ============================================================================
   Cardinality vs covering number for finite DyadicTube sets
   ============================================================================ -/

/-- For any finite DyadicTube family S, its cardinality is at most 5 times
    its δ-external covering number. -/
lemma card_le_five_cover {n : ℕ} (S : Finset (DyadicTube n)) :
    (S : Set (DyadicTube n)).encard ≤
      5 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S : Set (DyadicTube n)) := by
  let δ : NNReal := (dyadicDelta n).toNNReal
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_coe : (δ : ℝ) = dyadicDelta n := by
    have h : ((dyadicDelta n).toNNReal : ℝ) = dyadicDelta n := by
      simp [hδ_pos.le]
    exact h
  have h_main : ∀ (C : Set (DyadicTube n)),
      Metric.IsCover δ (S : Set (DyadicTube n)) C →
      (S : Set (DyadicTube n)).encard ≤ 5 * C.encard := by
    intro C hC
    by_cases hfin : C.Finite
    · let C' := hfin.toFinset
      have hC'_eq : (C' : Set (DyadicTube n)) = C := by exact Set.Finite.coe_toFinset hfin
      have hC' : Metric.IsCover δ (S : Set (DyadicTube n)) (C' : Set (DyadicTube n)) := by
        rw [hC'_eq] <;> exact hC
      have hcover : (S : Set (DyadicTube n)) ⊆
          ⋃ c ∈ (C' : Set (DyadicTube n)), Metric.closedBall c (δ : ℝ) :=
        hC'.subset_iUnion_closedBall
      have h1 : S ⊆ C'.biUnion (fun c => S.filter (fun T => T.dist c ≤ (δ : ℝ))) := by
        intro T hT
        have hT' : T ∈ (S : Set (DyadicTube n)) := by exact_mod_cast hT
        have h2 : T ∈ ⋃ c ∈ (C' : Set (DyadicTube n)), Metric.closedBall c (δ : ℝ) := hcover hT'
        have h3 : ∃ (c : DyadicTube n), c ∈ C' ∧ T ∈ Metric.closedBall c (δ : ℝ) := by
          simpa [Set.mem_iUnion] using h2
        rcases h3 with ⟨c, hc, h4⟩
        have h5 : T.dist c ≤ (δ : ℝ) := by
          have h6 : nndist T c ≤ δ := h4
          have h7 : dist T c ≤ (δ : ℝ) := by exact dist_le_coe.mpr h4
          exact h7
        have h_goal : T ∈ S.filter (fun T => T.dist c ≤ (δ : ℝ)) := by
          exact Finset.mem_filter.mpr ⟨hT, h5⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc, h_goal⟩
      have h2 : S.card ≤ ∑ c ∈ C', (S.filter (fun T => T.dist c ≤ (δ : ℝ))).card := by
        calc S.card
          ≤ (C'.biUnion (fun c => S.filter (fun T => T.dist c ≤ (δ : ℝ)))).card :=
            Finset.card_le_card h1
        _ ≤ ∑ c ∈ C', (S.filter (fun T => T.dist c ≤ (δ : ℝ))).card :=
            Finset.card_biUnion_le
      have h3 : ∀ c ∈ C', (S.filter (fun T => T.dist c ≤ (δ : ℝ))).card ≤ 5 := by
        intro c _
        have h4 : (δ : ℝ) = dyadicDelta n := hδ_coe
        rw [h4]
        exact ball_packing_bound c S
      have h4 : ∑ c ∈ C', (S.filter (fun T => T.dist c ≤ (δ : ℝ))).card ≤ ∑ c ∈ C', (5 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        exact h3 i ‹_›
      have h5 : ∑ c ∈ C', (5 : ℕ) = 5 * C'.card := by
        simp [Finset.sum_const] <;> ring
      have h6 : S.card ≤ 5 * C'.card := by linarith
      have h7 : C.encard = ↑C'.card := by
        have h8 : C.encard = (C' : Set (DyadicTube n)).encard := by rw [hC'_eq]
        rw [h8]
        simp
      rw [h7]
      exact_mod_cast h6
    · have hinf : C.Infinite := Set.not_finite.mp hfin
      have h9 : C.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr hfin
      rw [h9] <;> simp
  have h4 : (S : Set (DyadicTube n)).encard ≤
      ⨅ (C : Set (DyadicTube n)) (_ : Metric.IsCover δ (S : Set (DyadicTube n)) C),
        5 * C.encard := by
    apply le_iInf₂
    exact h_main
  have h5 : (⨅ (C : Set (DyadicTube n)) (_ : Metric.IsCover δ (S : Set (DyadicTube n)) C), 5 * C.encard) =
      5 * Metric.externalCoveringNumber δ (S : Set (DyadicTube n)) := by
    simp only [Metric.externalCoveringNumber]
    have h51 : ∀ (C : Set (DyadicTube n)),
        (5 * ⨅ (h : Metric.IsCover δ (S : Set (DyadicTube n)) C), C.encard) =
        ⨅ (h : Metric.IsCover δ (S : Set (DyadicTube n)) C), 5 * C.encard := by
      intro C
      rw [ENat.mul_iInf'] <;> simp
    calc (⨅ (C : Set (DyadicTube n)) (_ : Metric.IsCover δ (S : Set (DyadicTube n)) C), 5 * C.encard)
      = ⨅ (C : Set (DyadicTube n)), (⨅ (h : Metric.IsCover δ (S : Set (DyadicTube n)) C), 5 * C.encard) := by rfl
    _ = ⨅ (C : Set (DyadicTube n)), 5 * (⨅ (h : Metric.IsCover δ (S : Set (DyadicTube n)) C), C.encard) := by
        congr with C
        exact (h51 C).symm
    _ = 5 * ⨅ (C : Set (DyadicTube n)), (⨅ (h : Metric.IsCover δ (S : Set (DyadicTube n)) C), C.encard) := by
        rw [ENat.mul_iInf] <;> rfl
  rw [h5] at h4
  exact h4

/-! ============================================================================
   Discrete Frostman definition and transfer from IsDeltaSSet
   ============================================================================ -/

/-- Discrete Frostman condition using L1 metric on DyadicTubes. -/
def DiscreteFrostmanL1 {n : ℕ} (s C : ℝ) (F : Finset (DyadicTube n)) : Prop :=
  F.Nonempty ∧ 0 ≤ s ∧ 0 < C ∧
  ∀ (center : DyadicTube n) (r : ℝ), dyadicDelta n ≤ r →
    ((F.filter fun T => T.dist center ≤ r).card : ℝ) ≤ C * Real.rpow r s * (F.card : ℝ)

/-- IsDeltaSSet on a finite DyadicTube family implies DiscreteFrostmanL1
    with constant loss 5. -/
lemma isDeltaSSet_to_discreteFrostmanL1
    {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (h : IsDeltaSSet (dyadicDelta n) s C (F : Set (DyadicTube n))) :
    DiscreteFrostmanL1 s (5 * C) F := by
  rcases h with ⟨hF_nonempty, hδ_pos', hC_pos, hs, h_cover⟩
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  refine' ⟨hF_nonempty, hs, by positivity, _⟩
  intro center r hr
  let S_r := F.filter fun T => T.dist center ≤ r
  have h1 : (S_r : Set (DyadicTube n)) =
      (F : Set (DyadicTube n)) ∩ Metric.closedBall center r := by
    ext x; simp [S_r, Metric.mem_closedBall] <;> tauto
  set Ncover_Sr_nat : ℕ∞ := Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) with hNcover_Sr
  set Ncover_F_nat : ℕ∞ := Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n)) with hNcover_F
  let Ncover_Sr : ENNReal := ↑Ncover_Sr_nat
  let Ncover_F : ENNReal := ↑Ncover_F_nat
  let Crpow : ENNReal := ENNReal.ofReal C * (ENNReal.ofReal r) ^ s
  have h2_raw := h_cover center r hr
  have h2 : Ncover_Sr ≤ Crpow * Ncover_F := by
    have h_eq : (F : Set (DyadicTube n)) ∩ Metric.closedBall center r = (S_r : Set (DyadicTube n)) := h1.symm
    rw [h_eq] at h2_raw
    exact h2_raw
  have h4 : Ncover_F_nat ≤ (F : Set (DyadicTube n)).encard :=
    Metric.externalCoveringNumber_le_encard_self (F : Set (DyadicTube n))
  have h4' : Ncover_F ≤ ((F : Set (DyadicTube n)).encard : ENNReal) := by
    have h41 : (Ncover_F_nat : ENNReal) = Ncover_F := by rfl
    rw [←h41]
    exact_mod_cast h4
  have h_comb : Ncover_Sr ≤ Crpow * ((F : Set (DyadicTube n)).encard : ENNReal) := by
    calc Ncover_Sr
      ≤ Crpow * Ncover_F := h2
    _ ≤ Crpow * ((F : Set (DyadicTube n)).encard : ENNReal) := by
        exact mul_le_mul_of_nonneg_left h4' (by positivity)
  have h3 : (S_r : Set (DyadicTube n)).encard ≤ 5 * Ncover_Sr_nat := card_le_five_cover S_r
  have h3' : ((S_r : Set (DyadicTube n)).encard : ENNReal) ≤ (5 : ENNReal) * Ncover_Sr := by
    dsimp only [Ncover_Sr]
    exact_mod_cast h3
  have h5 : ((S_r : Set (DyadicTube n)).encard : ENNReal) ≤
      (5 : ENNReal) * (Crpow * ((F : Set (DyadicTube n)).encard : ENNReal)) := by
    calc ((S_r : Set (DyadicTube n)).encard : ENNReal)
      ≤ (5 : ENNReal) * Ncover_Sr := h3'
    _ ≤ (5 : ENNReal) * (Crpow * ((F : Set (DyadicTube n)).encard : ENNReal)) := by
        exact mul_le_mul_of_nonneg_left h_comb (by positivity)
  have hS_r_eq : ((S_r : Set (DyadicTube n)).encard : ENNReal) = (S_r.card : ENNReal) := by simp
  have hF_eq : ((F : Set (DyadicTube n)).encard : ENNReal) = (F.card : ENNReal) := by simp
  have h5' : (S_r.card : ENNReal) ≤ (5 : ENNReal) * (Crpow * (F.card : ENNReal)) := by
    rw [←hS_r_eq, ←hF_eq]
    exact h5
  have hC_nonneg : 0 ≤ C := by linarith
  have hr_nonneg : 0 ≤ r := by linarith [dyadicDelta_pos n, hr]
  have h_rhs_ne_top : (5 : ENNReal) * (Crpow * (F.card : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · apply ENNReal.mul_ne_top
      · have hCrpow_ne_top : Crpow ≠ ⊤ := by
          dsimp only [Crpow]
          apply ENNReal.mul_ne_top
          · simp
          · exact ENNReal.rpow_ne_top_of_nonneg hs (by simp)
        exact hCrpow_ne_top
      · simp
  have h10 : (S_r.card : ℝ) ≤ 5 * C * Real.rpow r s * (F.card : ℝ) := by
    have h11 : (S_r.card : ENNReal).toReal ≤ ((5 : ENNReal) * (Crpow * (F.card : ENNReal))).toReal := by
      rw [ENNReal.toReal_le_toReal (by simp) h_rhs_ne_top]
      exact h5'
    have hCrpow_real : Crpow.toReal = C * Real.rpow r s := by
      dsimp only [Crpow]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nonneg]
      have hpow : ((ENNReal.ofReal r) ^ s).toReal = Real.rpow r s := by
        have h : ((ENNReal.ofReal r) ^ s).toReal = (ENNReal.ofReal r).toReal ^ s :=
          (ENNReal.toReal_rpow (ENNReal.ofReal r) s).symm
        rw [h]
        have h2 : (ENNReal.ofReal r).toReal = r := by
          rw [ENNReal.toReal_ofReal hr_nonneg]
        rw [h2]
        <;> rfl
      rw [hpow] <;> ring
    have h12 : (S_r.card : ENNReal).toReal = (S_r.card : ℝ) := by simp
    have h13 : ((5 : ENNReal) * (Crpow * (F.card : ENNReal))).toReal =
        5 * Crpow.toReal * (F.card : ℝ) := by
      simp [ENNReal.toReal_mul] <;> ring
    rw [h12, h13] at h11
    rw [hCrpow_real] at h11
    have h14 : (S_r.card : ℝ) ≤ 5 * (C * Real.rpow r s) * (F.card : ℝ) := h11
    have h15 : 5 * (C * Real.rpow r s) * (F.card : ℝ) = 5 * C * Real.rpow r s * (F.card : ℝ) := by ring
    rw [h15] at h14
    exact h14
  simpa [S_r] using h10

/-! ============================================================================
   Standalone IsFiniteTubeSSet definition and transfer from DiscreteFrostmanL1
   ============================================================================ -/

/-- Standalone's IsFiniteTubeSSet: finite Frostman in L∞ parameter space
    with automatic δ-separation. -/
def IsFiniteTubeSSet {n : ℕ} (s C : ℝ) (F : Finset (DyadicTube n)) : Prop :=
  F.Nonempty ∧ 1 ≤ C ∧ 0 ≤ s ∧
  (∀ T ∈ F, ∀ U ∈ F, T ≠ U → dyadicDelta n ≤ tubeParamDistLinf T U) ∧
  ∀ center : DyadicTube n, ∀ r : ℝ, dyadicDelta n ≤ r →
    ((F.filter fun T => tubeParamDistLinf T center ≤ r).card : ℝ) ≤
      C * Real.rpow r s * (F.card : ℝ)

/-- Distinct DyadicTubes have L∞ parameter distance ≥ δ. -/
lemma linf_separated {n : ℕ} (T U : DyadicTube n) (h : T ≠ U) :
    dyadicDelta n ≤ tubeParamDistLinf T U := by
  have h1 : T.a ≠ U.a ∨ T.b ≠ U.b := by
    by_contra h2
    push Not at h2
    have h3 : T = U := by
      cases T <;> cases U <;> simp_all [DyadicTube.mk]
    exact h h3
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  rcases h1 with (h1 | h1)
  · have h2 : |(T.a : ℤ) - (U.a : ℤ)| ≥ 1 := by
      have h3 : (T.a : ℤ) ≠ (U.a : ℤ) := h1
      have h4 : 0 < |(T.a : ℤ) - (U.a : ℤ)| := abs_pos.mpr (sub_ne_zero.mpr h3)
      omega
    have h5 : |T.slope - U.slope| ≥ dyadicDelta n := by
      have h6 : T.slope - U.slope = dyadicDelta n * ((T.a : ℝ) - (U.a : ℝ)) := by
        simp [DyadicTube.slope] <;> ring
      rw [h6]
      have h7 : |dyadicDelta n * ((T.a : ℝ) - (U.a : ℝ))| =
          dyadicDelta n * |(T.a : ℝ) - (U.a : ℝ)| := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h7]
      have h8 : |(T.a : ℝ) - (U.a : ℝ)| ≥ 1 := by exact_mod_cast h2
      have h9 : dyadicDelta n * |(T.a : ℝ) - (U.a : ℝ)| ≥ dyadicDelta n := by
        have h10 : |(T.a : ℝ) - (U.a : ℝ)| ≥ 1 := by exact_mod_cast h2
        have h11 : 0 < dyadicDelta n := hδ_pos
        nlinarith
      linarith
    have h10 : tubeParamDistLinf T U ≥ |T.slope - U.slope| := by
      dsimp [tubeParamDistLinf]; exact le_max_left _ _
    linarith
  · have h2 : |(T.b : ℤ) - (U.b : ℤ)| ≥ 1 := by
      have h3 : (T.b : ℤ) ≠ (U.b : ℤ) := h1
      have h4 : 0 < |(T.b : ℤ) - (U.b : ℤ)| := abs_pos.mpr (sub_ne_zero.mpr h3)
      omega
    have h5 : |T.intercept - U.intercept| ≥ dyadicDelta n := by
      have h6 : T.intercept - U.intercept = dyadicDelta n * ((T.b : ℝ) - (U.b : ℝ)) := by
        simp [DyadicTube.intercept] <;> ring
      rw [h6]
      have h7 : |dyadicDelta n * ((T.b : ℝ) - (U.b : ℝ))| =
          dyadicDelta n * |(T.b : ℝ) - (U.b : ℝ)| := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h7]
      have h8 : |(T.b : ℝ) - (U.b : ℝ)| ≥ 1 := by exact_mod_cast h2
      have h9 : dyadicDelta n * |(T.b : ℝ) - (U.b : ℝ)| ≥ dyadicDelta n := by
        have h10 : |(T.b : ℝ) - (U.b : ℝ)| ≥ 1 := by exact_mod_cast h2
        have h11 : 0 < dyadicDelta n := hδ_pos
        nlinarith
      linarith
    have h10 : tubeParamDistLinf T U ≥ |T.intercept - U.intercept| := by
      dsimp [tubeParamDistLinf]; exact le_max_right _ _
    linarith

/-- DiscreteFrostmanL1 implies standalone IsFiniteTubeSSet
    with constant max 1 (2 * C). -/
lemma discreteFrostmanL1_to_isFiniteTubeSSet
    {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hs : s ≤ 1) (hs_nonneg : 0 ≤ s)
    (h : DiscreteFrostmanL1 s C F) :
    IsFiniteTubeSSet s (max 1 (2 * C)) F := by
  have hF_nonempty : F.Nonempty := h.1
  have hC_pos : 0 < C := h.2.2.1
  have hC'_one : 1 ≤ max 1 (2 * C) := by exact le_max_left _ _
  have h_sep : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → dyadicDelta n ≤ tubeParamDistLinf T U := by
    intro T _ U _ hne
    exact linf_separated T U hne
  have h_frost : ∀ center : DyadicTube n, ∀ r : ℝ, dyadicDelta n ≤ r →
      ((F.filter fun T => tubeParamDistLinf T center ≤ r).card : ℝ) ≤
        (max 1 (2 * C)) * Real.rpow r s * (F.card : ℝ) := by
    intro center r hr
    have h2r : dyadicDelta n ≤ 2 * r := by linarith [dyadicDelta_pos n]
    have h_sub : F.filter (fun T => tubeParamDistLinf T center ≤ r) ⊆
        F.filter (fun T => T.dist center ≤ 2 * r) := by
      intro T hT
      have h3 : tubeParamDistLinf T center ≤ r := (Finset.mem_filter.mp hT).2
      have h4 : T.dist center ≤ 2 * tubeParamDistLinf T center := dist_le_two_linf T center
      have h5 : T.dist center ≤ 2 * r := by linarith
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).1, h5⟩
    have h6 : (F.filter (fun T => tubeParamDistLinf T center ≤ r)).card ≤
        (F.filter (fun T => T.dist center ≤ 2 * r)).card := Finset.card_le_card h_sub
    have h7 : ((F.filter (fun T => T.dist center ≤ 2 * r)).card : ℝ) ≤
        C * Real.rpow (2 * r) s * (F.card : ℝ) := h.2.2.2 center (2 * r) h2r
    have h9 : 0 ≤ r := by linarith [dyadicDelta_pos n, hr]
    have h8 : Real.rpow (2 * r) s = (2 : ℝ)^s * Real.rpow r s := by
      have h81 : ((2 : ℝ) * r) ^ s = (2 : ℝ)^s * r ^ s := Real.mul_rpow (by norm_num) h9
      exact h81
    have h10 : (2 : ℝ)^s ≤ 2 := by
      have h11 : 0 ≤ s := hs_nonneg
      have h12 : s ≤ 1 := hs
      have h13 : (2 : ℝ)^s ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h12
      norm_num at h13 ⊢ <;> exact h13
    have h14 : ((F.filter (fun T => tubeParamDistLinf T center ≤ r)).card : ℝ) ≤
        (2 * C) * Real.rpow r s * (F.card : ℝ) := by
      calc ((F.filter (fun T => tubeParamDistLinf T center ≤ r)).card : ℝ)
        ≤ ((F.filter (fun T => T.dist center ≤ 2 * r)).card : ℝ) := by exact_mod_cast h6
      _ ≤ C * Real.rpow (2 * r) s * (F.card : ℝ) := h7
      _ = C * ((2 : ℝ)^s * Real.rpow r s) * (F.card : ℝ) := by rw [h8]
      _ = (C * (2 : ℝ)^s) * Real.rpow r s * (F.card : ℝ) := by ring
      _ ≤ (C * 2) * Real.rpow r s * (F.card : ℝ) := by
          have h15 : C * (2 : ℝ)^s ≤ C * 2 := by
            have h16 : (2 : ℝ)^s ≤ 2 := h10
            have h17 : 0 ≤ C := by linarith
            nlinarith
          have h18 : 0 ≤ Real.rpow r s := Real.rpow_nonneg h9 s
          have h19 : 0 ≤ (F.card : ℝ) := by positivity
          calc (C * (2 : ℝ)^s) * Real.rpow r s * (F.card : ℝ)
            = (C * (2 : ℝ)^s) * (Real.rpow r s * (F.card : ℝ)) := by ring
          _ ≤ (C * 2) * (Real.rpow r s * (F.card : ℝ)) := by
              exact mul_le_mul_of_nonneg_right h15 (by positivity)
          _ = (C * 2) * Real.rpow r s * (F.card : ℝ) := by ring
      _ = (2 * C) * Real.rpow r s * (F.card : ℝ) := by ring
    have h15 : (2 * C) ≤ max 1 (2 * C) := le_max_right _ _
    have h16 : 0 ≤ Real.rpow r s := Real.rpow_nonneg h9 s
    have h17 : 0 ≤ (F.card : ℝ) := by positivity
    calc ((F.filter (fun T => tubeParamDistLinf T center ≤ r)).card : ℝ)
      ≤ (2 * C) * Real.rpow r s * (F.card : ℝ) := h14
    _ ≤ (max 1 (2 * C)) * Real.rpow r s * (F.card : ℝ) := by
        have h18 : (2 * C) ≤ max 1 (2 * C) := le_max_right _ _
        nlinarith
  exact ⟨hF_nonempty, hC'_one, hs_nonneg, h_sep, h_frost⟩

/-! ============================================================================
   Reverse transfer: IsFiniteTubeSSet → IsDeltaSSet

   Since F is δ-separated in L∞ and L∞ ≤ L1, F is δ-separated in L1.
   For any L1 ball of radius r:
     |F ∩ ball_L1(x,r)| ≤ |F ∩ ball_L∞(x,r)| ≤ C * r^s * |F|
   And Ncover(δ, S) ≤ |S|, |F| ≤ 5 * Ncover(δ, F).
   Thus Ncover(δ, F ∩ ball_L1(x,r)) ≤ 5C * r^s * Ncover(δ, F).
   ============================================================================ -/

/-- Reverse transfer: standalone IsFiniteTubeSSet → main IsDeltaSSet
    with constant 5 * C. -/
lemma isFiniteTubeSSet_to_isDeltaSSet
    {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hC_one : 1 ≤ C)
    (h : IsFiniteTubeSSet s C F) :
    IsDeltaSSet (dyadicDelta n) s (5 * C) (F : Set (DyadicTube n)) := by
  have hF_nonempty : F.Nonempty := h.1
  have hC_pos : 0 < C := by linarith
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_frost : ∀ center : DyadicTube n, ∀ r : ℝ, dyadicDelta n ≤ r →
      ((F.filter fun T => tubeParamDistLinf T center ≤ r).card : ℝ) ≤
      C * Real.rpow r s * (F.card : ℝ) := h.2.2.2.2
  have hC_nonneg : 0 ≤ C := by linarith
  have hr_nonneg : ∀ (r : ℝ), dyadicDelta n ≤ r → 0 ≤ r := by
    intro r hr; linarith [hδ_pos]
  refine' ⟨hF_nonempty, hδ_pos, by positivity, hs, _⟩
  intro x r hr
  let S_r := F.filter fun T => T.dist x ≤ r
  have hS_r_eq : (S_r : Set (DyadicTube n)) =
      (F : Set (DyadicTube n)) ∩ Metric.closedBall x r := by
    ext y; simp [S_r, Metric.mem_closedBall] <;> tauto
  -- S_r ⊆ L∞ ball filter
  have h1 : S_r ⊆ F.filter fun T => tubeParamDistLinf T x ≤ r := by
    intro T hT
    have h2 : T.dist x ≤ r := (Finset.mem_filter.mp hT).2
    have h3 : tubeParamDistLinf T x ≤ T.dist x := linf_le_dist T x
    have h4 : tubeParamDistLinf T x ≤ r := by linarith
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).1, h4⟩
  have h6 : S_r.card ≤ (F.filter fun T => tubeParamDistLinf T x ≤ r).card :=
    Finset.card_le_card h1
  have h7 : ((F.filter fun T => tubeParamDistLinf T x ≤ r).card : ℝ) ≤
      C * Real.rpow r s * (F.card : ℝ) := h_frost x r hr
  have h5 : (S_r.card : ℝ) ≤ C * Real.rpow r s * (F.card : ℝ) := by
    have h6' : (S_r.card : ℝ) ≤ ((F.filter fun T => tubeParamDistLinf T x ≤ r).card : ℝ) := by
      exact_mod_cast h6
    exact le_trans h6' h7
  -- Ncover(S_r) ≤ |S_r| (as ℕ∞, then coerce to ENNReal)
  have h81 : Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) ≤
      (S_r.card : ℕ∞) := by
    have h : Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) ≤
        (S_r : Set (DyadicTube n)).encard :=
      Metric.externalCoveringNumber_le_encard_self (ε := (dyadicDelta n).toNNReal) (S_r : Set (DyadicTube n))
    have h2 : (S_r : Set (DyadicTube n)).encard = (S_r.card : ℕ∞) := by simp
    rw [h2] at h
    exact h
  have h8 : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) : ENNReal) ≤
      (S_r.card : ENNReal) := by
    exact_mod_cast h81
  -- |F| ≤ 5 * Ncover(F)
  have h91 : (F.card : ℕ∞) ≤
      5 * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n)) := by
    have h := card_le_five_cover F
    have h2 : (F : Set (DyadicTube n)).encard = (F.card : ℕ∞) := by simp
    rw [h2] at h
    exact h
  have h9 : (F.card : ENNReal) ≤
      (5 : ENNReal) * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n)) := by
    exact_mod_cast h91
  -- ofReal rpow lemma
  have h12 : 0 ≤ r := hr_nonneg r hr
  have h13_rpow : 0 ≤ Real.rpow r s := Real.rpow_nonneg h12 s
  have h_rpow_toReal : ((ENNReal.ofReal r) ^ s).toReal = Real.rpow r s := by
    have h : (ENNReal.ofReal r).toReal ^ s = ((ENNReal.ofReal r) ^ s).toReal :=
      ENNReal.toReal_rpow (ENNReal.ofReal r) s
    have h2 : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal h12
    rw [h2] at h
    exact h.symm
  have h_rpow : ENNReal.ofReal (Real.rpow r s) = (ENNReal.ofReal r) ^ s := by
    have h3 : (ENNReal.ofReal (Real.rpow r s)) ≠ ⊤ := by simp
    have h4 : ((ENNReal.ofReal r) ^ s) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs (by simp)
    have h5 : (ENNReal.ofReal (Real.rpow r s)).toReal = ((ENNReal.ofReal r) ^ s).toReal := by
      rw [ENNReal.toReal_ofReal h13_rpow, h_rpow_toReal]
    have h6 : ENNReal.ofReal (Real.rpow r s) = (ENNReal.ofReal r) ^ s := by
      exact Eq.symm ((fun {x y} hx hy => (ENNReal.toReal_eq_toReal_iff' hx hy).mp) h4 h3 (id (Eq.symm h5)))
    exact h6
  -- Lift h5 to ENNReal
  have h10 : (S_r.card : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (F.card : ENNReal) := by
    have h13 : ENNReal.ofReal (S_r.card : ℝ) ≤
        ENNReal.ofReal (C * Real.rpow r s * (F.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h5
    have h14 : ENNReal.ofReal (C * Real.rpow r s * (F.card : ℝ)) =
        ENNReal.ofReal C * ENNReal.ofReal (Real.rpow r s) * ENNReal.ofReal (F.card : ℝ) := by
      have h141 : 0 ≤ C := hC_nonneg
      have h142 : 0 ≤ Real.rpow r s := h13_rpow
      have h143 : 0 ≤ (F.card : ℝ) := by positivity
      rw [show C * Real.rpow r s * (F.card : ℝ) = (C * Real.rpow r s) * (F.card : ℝ) by ring]
      rw [ENNReal.ofReal_mul (show 0 ≤ C * Real.rpow r s from by positivity),
          ENNReal.ofReal_mul h141]
      <;> ring
    rw [h14, h_rpow] at h13
    simpa using h13
  -- Combine
  have h16 : (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) : ENNReal) ≤
      ENNReal.ofReal (5 * C) * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n)) := by
    calc (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (S_r : Set (DyadicTube n)) : ENNReal)
      ≤ (S_r.card : ENNReal) := h8
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (F.card : ENNReal) := h10
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((5 : ENNReal) * Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n))) := by
      gcongr
    _ = (5 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n))) := by ring
    _ = ENNReal.ofReal (5 * C) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (dyadicDelta n).toNNReal (F : Set (DyadicTube n)) := by
      have h17 : ENNReal.ofReal (5 * C) = (5 : ENNReal) * ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        <;> simp [mul_comm]
        <;> ring
      rw [h17] <;> ring
  simpa [hS_r_eq] using h16

end DiscretisedFurstenbergEstimate.InductionOnScales
