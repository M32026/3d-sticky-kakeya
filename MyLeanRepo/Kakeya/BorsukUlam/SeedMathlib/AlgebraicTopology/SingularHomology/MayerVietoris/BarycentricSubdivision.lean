/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.CategoryTheory.Balanced
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section


/-!
# Cone construction on singular chains

Given a point `b` in a convex set `s`, we can form the cone `b * σ` of a singular
simplex `σ : Δᵏ → s`, which is a singular (k+1)-simplex `Δ^{k+1} → s`.

This is the fundamental technical tool for barycentric subdivision.
-/

noncomputable section

open scoped Simplicial

namespace AlgebraicTopology

/-- Given a point `t` in the (k+1)-dimensional standard simplex with `t 0 ≠ 1`,
project onto the k-dimensional face opposite vertex 0. -/
def stdSimplex.face0Proj (k : ℕ)
    (t : {x // x ∈ stdSimplex ℝ (Fin (k + 2))})
    (ht : t.val 0 ≠ 1) :
    {x // x ∈ stdSimplex ℝ (Fin (k + 1))} :=
  let t0 : ℝ := t.val 0
  let f : Fin (k + 1) → ℝ := fun i => t.val (Fin.succ i) / (1 - t0)
  have h_nonneg : ∀ i : Fin (k + 1), 0 ≤ f i := by
    intro i
    apply div_nonneg
    · exact t.prop.1 (Fin.succ i)
    · have h : t0 ≤ 1 := by
        have h_sum : ∑ j : Fin (k + 2), t.val j = 1 := t.prop.2
        have : t.val 0 ≤ ∑ j : Fin (k + 2), t.val j :=
          Finset.single_le_sum (fun j _ => t.prop.1 j) (Finset.mem_univ 0)
        rw [h_sum] at this
        exact this
      linarith
  have h_sum1 : ∑ i : Fin (k + 1), f i = 1 := by
    dsimp only [f]
    have h_sum_div : ∑ i : Fin (k + 1), (t.val (Fin.succ i) / (1 - t0)) =
        (∑ i : Fin (k + 1), t.val (Fin.succ i)) / (1 - t0) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    rw [h_sum_div]
    have h' : ∑ i : Fin (k + 1), t.val (Fin.succ i) = 1 - t0 := by
      have h_total : ∑ j : Fin (k + 2), t.val j = 1 := t.prop.2
      have : ∑ j : Fin (k + 2), t.val j = t.val 0 + ∑ i : Fin (k + 1), t.val (Fin.succ i) := by
        rw [Fin.sum_univ_succ]
      rw [this] at h_total
      linarith
    rw [h']
    have h1t : 1 - t0 ≠ 0 := by
      intro h2
      have : t0 = 1 := by linarith
      exact ht this
    field_simp [h1t]
  ⟨f, ⟨h_nonneg, h_sum1⟩⟩

/-- The cone of a singular simplex `σ : Δᵏ → E` with apex `b ∈ s`,
where `s` is convex in a real normed space `E`.
This is a map from the (k+1)-dimensional standard simplex to `E`. -/
def singularCone {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    (σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E) :
    {x // x ∈ stdSimplex ℝ (Fin (k + 2))} → E :=
  fun t : {x // x ∈ stdSimplex ℝ (Fin (k + 2))} =>
    let t0 : ℝ := t.val 0
    if h : t0 = 1 then
      b
    else
      t0 • b + (1 - t0) • σ (stdSimplex.face0Proj k t h)

theorem singularCone_mem {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} {k : ℕ}
    (hs : Convex ℝ s) (hb : b ∈ s)
    (σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E)
    (hσ : ∀ x, σ x ∈ s)
    (t : {x // x ∈ stdSimplex ℝ (Fin (k + 2))}) :
    singularCone (b := b) σ t ∈ s := by
  dsimp only [singularCone]
  let t0 : ℝ := t.val 0
  by_cases h : t0 = 1
  · rw [dif_pos h]
    exact hb
  · rw [dif_neg h]
    have h1 : 0 ≤ t0 := t.prop.1 0
    have h2 : t0 ≤ 1 := by
      have h_sum : ∑ i : Fin (k + 2), t.val i = 1 := t.prop.2
      have : t.val 0 ≤ ∑ i : Fin (k + 2), t.val i :=
        Finset.single_le_sum (fun i _ => t.prop.1 i) (Finset.mem_univ 0)
      rw [h_sum] at this
      exact this
    have h3 : 0 ≤ 1 - t0 := by linarith
    have h4 : σ (stdSimplex.face0Proj k t h) ∈ s := hσ (stdSimplex.face0Proj k t h)
    have h5 : t0 + (1 - t0) = 1 := by linarith
    exact hs hb h4 h1 h3 h5

/-- Norm estimate for the cone: `‖cone(b,σ)(t) - b‖ ≤ abs(1 - t₀) * M`
where `M` bounds `‖σ(x) - b‖`. -/
lemma singularCone_norm_estimate {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E}
    (M : ℝ) (hM : ∀ x, ‖σ x - b‖ ≤ M)
    (t : {x // x ∈ stdSimplex ℝ (Fin (k + 2))}) :
    ‖singularCone (b := b) σ t - b‖ ≤ abs (1 - t.val 0) * M := by
  dsimp only [singularCone]
  let t0 : ℝ := t.val 0
  by_cases h : t0 = 1
  · rw [dif_pos h]
    have h' : abs (1 - t0) = 0 := by
      rw [show (1 - t0) = 0 by linarith]
      simp
    rw [h']
    ; simp
  · rw [dif_neg h]
    have h1 : t0 • b + (1 - t0) • σ (stdSimplex.face0Proj k t h) - b =
        (1 - t0) • (σ (stdSimplex.face0Proj k t h) - b) := by
      simp [smul_sub, sub_smul]
      ; abel
    rw [h1]
    have h2 : ‖(1 - t0) • (σ (stdSimplex.face0Proj k t h) - b)‖ =
        abs (1 - t0) * ‖σ (stdSimplex.face0Proj k t h) - b‖ := by
      rw [norm_smul]
      ; rfl
    rw [h2]
    have h3 : ‖σ (stdSimplex.face0Proj k t h) - b‖ ≤ M := hM (stdSimplex.face0Proj k t h)
    have h4 : 0 ≤ abs (1 - t0) := abs_nonneg (1 - t0)
    exact mul_le_mul_of_nonneg_left h3 h4

theorem singularCone_continuous {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E}
    (hσ_cont : Continuous σ) :
    Continuous (singularCone (b := b) σ) := by
  let S2 := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
  let S1 := {x // x ∈ stdSimplex ℝ (Fin (k + 1))}
  -- The domain of σ is compact, so ‖σ x - b‖ is bounded
  have h_bdd : ∃ (M : ℝ), ∀ (x : S1), ‖σ x - b‖ ≤ M := by
    let f : S1 → ℝ := fun x => ‖σ x - b‖
    have hf_cont : Continuous f := continuous_norm.comp (hσ_cont.sub continuous_const)
    have h_compact : IsCompact (Set.univ : Set S1) := isCompact_univ
    have h1 : BddAbove (Set.range f) := by
      have h2 : f '' Set.univ = Set.range f := by
        ext x
        simp
      rw [←h2]
      exact (h_compact.image hf_cont).bddAbove
    refine ⟨sSup (Set.range f), fun x => ?_⟩
    exact le_csSup h1 (Set.mem_range_self x)
  rcases h_bdd with ⟨M, hM⟩
  have h_main : ∀ (t₁ : S2), ContinuousAt (singularCone (b := b) σ) t₁ := by
    intro t₁
    by_cases h_apex : t₁.val 0 = 1
    · -- Case 1: t₁ is the apex point (t₁.val 0 = 1)
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hM_nonneg : 0 ≤ M := by
        have h_nonempty : Nonempty S1 := by
          refine ⟨⟨fun _ => (1 : ℝ) / (k + 1 : ℝ), ?_⟩⟩
          constructor
          · intro i
            positivity
          · have h_sum : ∑ i : Fin (k + 1), (1 : ℝ) / (k + 1 : ℝ) = 1 := by
              have h1 : ∑ i : Fin (k + 1), (1 : ℝ) / (k + 1 : ℝ) =
                  (Finset.card (Finset.univ : Finset (Fin (k + 1))) : ℝ) * ((1 : ℝ) / (k + 1 : ℝ)) := by
                rw [Finset.sum_const]
                ; ring
              rw [h1]
              have h2 : (Finset.card (Finset.univ : Finset (Fin (k + 1))) : ℝ) = (k + 1 : ℝ) := by
                simp
              rw [h2]
              have h_pos : (0 : ℝ) < (k + 1 : ℝ) := by positivity
              field_simp
            exact h_sum
        rcases h_nonempty with ⟨x⟩
        have h2 : ‖σ x - b‖ ≤ M := hM x
        have h3 : 0 ≤ ‖σ x - b‖ := norm_nonneg _
        linarith
      let ε' := ε / (M + 1)
      have hε'_pos : 0 < ε' := by positivity
      have h_eval_cont : Continuous (fun (t : S2) => t.val 0) :=
        (continuous_apply 0).comp continuous_subtype_val
      have h : ∃ δ > 0, ∀ (t : S2), dist t t₁ < δ → abs (t.val 0 - t₁.val 0) < ε' :=
        Metric.continuousAt_iff.mp (h_eval_cont.continuousAt) ε' hε'_pos
      rcases h with ⟨δ, hδ_pos, hδ⟩
      use δ, hδ_pos
      intro t ht
      have h5 : abs (t.val 0 - t₁.val 0) < ε' := hδ t ht
      rw [h_apex] at h5
      have h_apex_val : singularCone (b := b) σ t₁ = b := by
        dsimp only [singularCone]
        rw [dif_pos h_apex]
      have h_goal : dist (singularCone (b := b) σ t) (singularCone (b := b) σ t₁) =
          ‖singularCone (b := b) σ t - b‖ := by
        rw [h_apex_val, dist_eq_norm]
      rw [h_goal]
      have h8 : ‖singularCone (b := b) σ t - b‖ ≤ abs (1 - t.val 0) * M :=
        singularCone_norm_estimate M hM t
      have h9 : abs (1 - t.val 0) = abs (t.val 0 - 1) := by
        rw [show (1 - t.val 0) = -(t.val 0 - 1) by ring]
        rw [abs_neg]
      rw [h9] at h8
      have h10 : abs (t.val 0 - 1) < ε' := h5
      have h11 : abs (t.val 0 - 1) * M < ε := by
        have h12 : 0 ≤ M := hM_nonneg
        have h13 : abs (t.val 0 - 1) * M ≤ abs (t.val 0 - 1) * (M + 1) := by
          gcongr ; linarith
        have h14 : abs (t.val 0 - 1) * (M + 1) < ε := by
          have h_pos : 0 < M + 1 := by linarith
          have h15 : abs (t.val 0 - 1) * (M + 1) < ε' * (M + 1) :=
            mul_lt_mul_of_pos_right h10 h_pos
          rw [show ε' = ε / (M + 1) from rfl] at h15
          have h16 : (ε / (M + 1)) * (M + 1) = ε := by
            field_simp
          rw [h16] at h15
          exact h15
        linarith
      exact lt_of_le_of_lt h8 h11
    · -- Case 2: t₁.val 0 ≠ 1
      let U : Set S2 := {t | t.val 0 ≠ 1}
      have hU_open : IsOpen U := by
        have h1 : IsOpen ({(1 : ℝ)}ᶜ : Set ℝ) := isOpen_compl_singleton
        have h2 : Continuous (fun (t : S2) => t.val 0) :=
          (continuous_apply 0).comp continuous_subtype_val
        exact h2.isOpen_preimage _ h1
      have h_t1_in_U : t₁ ∈ U := h_apex
      -- Use subtype of U to define continuous face projection
      let U' := {t : S2 // t.val 0 ≠ 1}
      let g : U' → S1 := fun x => stdSimplex.face0Proj k x.val x.property
      have hg_cont : Continuous g := by
        apply Continuous.subtype_mk
        · apply continuous_pi
          intro i
          have h : Continuous (fun (x : U') => x.val.val (Fin.succ i) / (1 - x.val.val 0)) := by
            apply Continuous.div
            · exact (continuous_apply (Fin.succ i)).comp
                (continuous_subtype_val.comp continuous_subtype_val)
            · exact continuous_const.sub ((continuous_apply 0).comp
                (continuous_subtype_val.comp continuous_subtype_val))
            · intro x
              have h_ne : x.val.val 0 ≠ 1 := x.property
              intro h_contra
              have h9 : x.val.val 0 = 1 := by linarith
              exact h_ne h9
          exact h

      let f : U' → E := fun x =>
        x.val.val 0 • b + (1 - x.val.val 0) • σ (g x)
      have h1_cont : Continuous (fun (x : U') => x.val.val 0) :=
        (continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)
      have h2_cont : Continuous (fun (x : U') => (1 : ℝ) - x.val.val 0) :=
        continuous_const.sub h1_cont
      have h3_cont : Continuous (fun (x : U') => σ (g x)) := hσ_cont.comp hg_cont
      have h4_cont : Continuous (fun (x : U') => x.val.val 0 • b) := h1_cont.smul continuous_const
      have h5_cont : Continuous (fun (x : U') => (1 - x.val.val 0) • σ (g x)) :=
        h2_cont.smul h3_cont
      have hf_cont : Continuous f := h4_cont.add h5_cont
      have h_eq : ∀ (x : U'), singularCone (b := b) σ x.val = f x := by
        intro x
        dsimp only [singularCone, f]
        rw [dif_neg x.property]
      have h_contOn : ContinuousOn (singularCone (b := b) σ) U := by
        rw [continuousOn_iff_continuous_restrict]
        have h_eq2 : Set.restrict U (singularCone (b := b) σ) = f := by
          funext x
          exact h_eq x
        exact h_eq2 ▸ hf_cont
      have h_contAt : ContinuousAt (singularCone (b := b) σ) t₁ :=
        h_contOn.continuousAt (hU_open.mem_nhds h_t1_in_U)
      exact h_contAt
  rw [continuous_iff_continuousAt]
  exact h_main

/-! ### Face maps and cone boundary formula -/

/-- The i-th face inclusion map on standard simplices. -/
def stdSimplex.faceMap {k : ℕ} (i : Fin (k + 2)) :
    {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → {x // x ∈ stdSimplex ℝ (Fin (k + 2))} :=
  stdSimplex.map (Fin.succAbove i)

/-- The face map is continuous. -/
lemma stdSimplex.continuous_faceMap {k : ℕ} (i : Fin (k + 2)) :
    Continuous (stdSimplex.faceMap i) :=
  stdSimplex.continuous_map (Fin.succAbove i)

/-- Face 0 of the cone `b * σ` is just `σ` (the base of the cone). -/
theorem singularCone_face0 {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E}
    (x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}) :
    singularCone (b := b) σ (stdSimplex.faceMap (0 : Fin (k + 2)) x) = σ x := by
  let t := stdSimplex.faceMap (0 : Fin (k + 2)) x
  have h_succAbove_eq : (Fin.succAbove (0 : Fin (k + 2))) = Fin.succ := by
    funext i
    exact Fin.zero_succAbove i
  have h_map_val : ∀ (y : Fin (k + 2)), t.val y =
      (Finset.univ.filter (fun (x' : Fin (k + 1)) ↦ Fin.succ x' = y)).sum (fun x' => x.val x') := by
    intro y
    have h1 : t.val y = FunOnFinite.linearMap ℝ ℝ (Fin.succAbove (0 : Fin (k + 2))) x.val y := by
      simp
      ; rfl
    rw [h1, h_succAbove_eq]
    have h2 : FunOnFinite.linearMap ℝ ℝ (Fin.succ : Fin (k + 1) → Fin (k + 2)) x.val y =
        (Finset.univ.filter (fun (x' : Fin (k + 1)) ↦ Fin.succ x' = y)).sum (fun x' => x.val x') := by
      exact FunOnFinite.linearMap_apply_apply ℝ ℝ Fin.succ (↑x) y
    exact h2
  have h_t0 : t.val 0 = 0 := by
    rw [h_map_val 0]
    have h_empty : Finset.univ.filter (fun (x' : Fin (k + 1)) ↦ Fin.succ x' = (0 : Fin (k + 2))) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x' _
      simp
    rw [h_empty]
    ; simp
  have h_ne_one : t.val 0 ≠ 1 := by
    rw [h_t0] ; norm_num
  have h_face_succ : ∀ (i : Fin (k + 1)), t.val (Fin.succ i) = x.val i := by
    intro i
    rw [h_map_val (Fin.succ i)]
    have h_filter : Finset.univ.filter (fun (x' : Fin (k + 1)) ↦ Fin.succ x' = Fin.succ i) = {i} := by
      ext j
      simp [Fin.succ_inj]
    rw [h_filter]
    ; simp
  have h_face0Proj : stdSimplex.face0Proj k t h_ne_one = x := by
    apply Subtype.ext
    ext i
    dsimp only [stdSimplex.face0Proj]
    rw [Subtype.coe_mk]
    have h_div : (t.val (Fin.succ i)) / (1 - t.val 0) = x.val i := by
      rw [h_face_succ i, h_t0]
      have h : (x.val i) / (1 - (0 : ℝ)) = x.val i := by
        have h' : (1 - (0 : ℝ)) = 1 := by norm_num
        rw [h']
        ; ring
      exact h
    exact h_div
  have h_main : singularCone (b := b) σ t = σ x := by
    dsimp only [singularCone]
    rw [dif_neg h_ne_one]
    rw [h_face0Proj, h_t0]
    ; simp
  exact h_main

/-- Key lemma: `Fin.succAbove (Fin.succ j) ⁻¹' {Fin.succ m} = Fin.succ '' (Fin.succAbove j ⁻¹' {m})`. -/
lemma fin_succAbove_comm {n : ℕ} (j m : Fin (n + 2)) :
    Finset.univ.filter (fun (z : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) z = Fin.succ m) =
    Finset.image Fin.succ (Finset.univ.filter (fun (y : Fin (n + 1)) ↦ Fin.succAbove j y = m)) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · -- Forward direction
    intro h
    have h_eq : Fin.succAbove (Fin.succ j) z = Fin.succ m := h
    by_cases h_le : z ≤ j
    · -- Case z ≤ j
      have h1 : Fin.succAbove (Fin.succ j) z = z.castSucc :=
        Fin.succAbove_succ_of_le j z h_le
      have h2 : z.castSucc = Fin.succ m := by rw [←h1, h_eq]
      have h3 : (z.castSucc).val = (Fin.succ m).val := by rw [h2]
      have h4 : (z.castSucc).val = z.val := by rfl
      have h5 : (Fin.succ m).val = m.val + 1 := by simp
      have h6 : z.val = m.val + 1 := by
        rw [←h4, ←h5]
        exact h3
      have h7 : m.val < j.val := by omega
      have h8 : m.val < n + 1 := by omega
      let y : Fin (n + 1) := ⟨m.val, by omega⟩
      have h9 : y.val = m.val := by simp [y]
      have h10 : y.castSucc < j := by
        have h101 : (y.castSucc).val = y.val := by rfl
        have h102 : (y.castSucc).val < j.val := by
          rw [h101, h9]
          exact h7
        exact Fin.castSucc_lt_iff_succ_le.mpr h7
      have h11 : Fin.succAbove j y = y.castSucc := Fin.succAbove_of_castSucc_lt j y h10
      have h13 : Fin.succAbove j y = m := by
        rw [h11]
        apply Fin.ext
        have h14 : (y.castSucc).val = y.val := by rfl
        rw [h14, h9]
      have h15 : Fin.succ y = z := by
        apply Fin.ext
        simp [y, h6]
      exact ⟨y, h13, h15⟩
    · -- Case ¬(z ≤ j), i.e. j < z
      have h_gt : j < z := by exact Fin.not_le.mp h_le
      have h1 : Fin.succAbove (Fin.succ j) z = z.succ :=
        Fin.succAbove_succ_of_lt j z h_gt
      have h2 : z.succ = Fin.succ m := by rw [←h1, h_eq]
      have h3 : (z.succ).val = (Fin.succ m).val := by rw [h2]
      have h4 : (z.succ).val = z.val + 1 := by simp
      have h5 : (Fin.succ m).val = m.val + 1 := by simp
      have h6 : z.val = m.val := by
        have h61 : (z.succ).val = z.val + 1 := h4
        have h62 : (Fin.succ m).val = m.val + 1 := h5
        linarith [h3, h61, h62]
      have h7 : j.val < m.val := by omega
      have h8 : 1 ≤ m.val := by omega
      have h9 : m.val - 1 ≤ n := by omega
      let y : Fin (n + 1) := ⟨m.val - 1, by omega⟩
      have h10 : y.val = m.val - 1 := by simp [y]
      have h11 : j ≤ y.castSucc := by
        rw [Fin.le_iff_val_le_val]
        have h12 : (y.castSucc).val = y.val := by rfl
        rw [h12, h10]
        ; omega
      have h13 : Fin.succAbove j y = y.succ := Fin.succAbove_of_le_castSucc j y h11
      have h14 : y.succ = m := by
        apply Fin.ext
        simp [y] ; omega
      have h15 : Fin.succAbove j y = m := by
        rw [h13, h14]
      have h16 : Fin.succ y = z := by
        apply Fin.ext
        simp [y, h6] ; omega
      exact ⟨y, h15, h16⟩
  · -- Backward direction
    rintro ⟨y, hy, rfl⟩
    have h_y_in : Fin.succAbove j y = m := hy
    by_cases h_lt : y.castSucc < j
    · -- Case y.castSucc < j
      have h1 : Fin.succAbove j y = y.castSucc := Fin.succAbove_of_castSucc_lt j y h_lt
      have h2 : y.castSucc = m := by rw [←h1, h_y_in]
      have h3 : (y.castSucc).val = m.val := by
        exact congr_arg (fun x : Fin (n + 2) => x.val) h2
      have h4 : y.val = m.val := by
        have h5 : (y.castSucc).val = y.val := by rfl
        rw [h5] at h3
        exact h3
      have h6 : (Fin.succ y).val ≤ j.val := by
        have h7 : (Fin.succ y).val = y.val + 1 := by simp
        rw [h7, h4]
        ; omega
      have h8 : Fin.succ y ≤ j := by exact Fin.castSucc_lt_iff_succ_le.mp h_lt
      have h9 : Fin.succAbove (Fin.succ j) (Fin.succ y) = (Fin.succ y).castSucc :=
        Fin.succAbove_succ_of_le j (Fin.succ y) h8
      rw [h9]
      apply Fin.ext
      have h10 : ((Fin.succ y).castSucc).val = (Fin.succ y).val := by rfl
      have h11 : (Fin.succ m).val = m.val + 1 := by simp
      rw [h10, h11]
      have h12 : (Fin.succ y).val = y.val + 1 := by simp
      rw [h12, h4]
    · -- Case ¬(y.castSucc < j), i.e. j ≤ y.castSucc
      have h_ge : j ≤ y.castSucc := by exact Fin.not_lt.mp h_lt
      have h1 : Fin.succAbove j y = y.succ := Fin.succAbove_of_le_castSucc j y h_ge
      have h2 : y.succ = m := by rw [←h1, h_y_in]
      have h3 : (y.succ).val = m.val := by
        exact congr_arg (fun x : Fin (n + 2) => x.val) h2
      have h4 : j.val < (Fin.succ y).val := by
        have h5 : j.val ≤ y.val := by exact Nat.not_lt.mp h_lt
        have h6 : (Fin.succ y).val = y.val + 1 := by simp
        rw [h6]
        ; omega
      have h7 : ¬(Fin.succ y ≤ j) := by exact Fin.not_le.mpr h4
      have h8 : Fin.succAbove (Fin.succ j) (Fin.succ y) = (Fin.succ y).succ :=
        Fin.succAbove_succ_of_lt j (Fin.succ y) (by exact Fin.le_castSucc_iff.mp h_ge)
      rw [h8]
      apply Fin.ext
      have h9 : ((Fin.succ y).succ).val = (Fin.succ y).val + 1 := by simp
      have h10 : (Fin.succ m).val = m.val + 1 := by simp
      rw [h9, h10]
      have h11 : (Fin.succ y).val = y.val + 1 := by simp
      have h12 : m.val = y.val + 1 := by
        have h13 : (y.succ).val = y.val + 1 := by simp
        rw [h13] at h3
        exact h3.symm
      rw [h11, h12]

/-- The 0-th coordinate is unchanged by face maps with index > 0. -/
lemma stdSimplex.faceMap_val0 {n : ℕ} (j : Fin (n + 2))
    (x : {x // x ∈ stdSimplex ℝ (Fin (n + 2))}) :
    (stdSimplex.faceMap (Fin.succ j) x).val 0 = x.val 0 := by
  have h_map_val : ∀ (y : Fin (n + 3)), (stdSimplex.faceMap (Fin.succ j) x).val y =
      (Finset.univ.filter (fun (x' : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) x' = y)).sum
        (fun x' => x.val x') := by
    intro y
    have h1 : (stdSimplex.faceMap (Fin.succ j) x).val y =
        FunOnFinite.linearMap ℝ ℝ (Fin.succAbove (Fin.succ j)) x.val y := by
      simp [stdSimplex.faceMap]
      ; rfl
    rw [h1]
    exact FunOnFinite.linearMap_apply_apply ℝ ℝ j.succ.succAbove (↑x) y
  rw [h_map_val 0]
  have h_filter : Finset.univ.filter (fun (x' : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) x' = 0) = {0} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have h2 : Fin.succAbove (Fin.succ j) z = 0 := h
      have h3 : (Fin.succAbove (Fin.succ j) z).val = 0 := by rw [h2] ; rfl
      have h4 : z.val = 0 := by
        by_cases h5 : z ≤ j
        · have h6 : (Fin.succAbove (Fin.succ j) z).val = z.val := by
            simp [Fin.succAbove, h5]
          rw [h6] at h3
          exact h3
        · have h6 : (Fin.succAbove (Fin.succ j) z).val = z.val + 1 := by
            simp [Fin.succAbove, h5]
          rw [h6] at h3
          ; omega
      exact Fin.ext h4
    · intro h
      rw [h]
      have h5 : Fin.succAbove (Fin.succ j) (0 : Fin (n + 2)) = 0 := by
        apply Fin.ext
        simp [Fin.succAbove]
      exact h5
  rw [h_filter]
  ; simp

/-- `face0Proj` commutes with `faceMap j` for j > 0:
projecting onto face 0 after inserting face j+1 is the same as
inserting face j after projecting onto face 0. -/
lemma stdSimplex.face0Proj_comm_faceMap {n : ℕ}
    (j : Fin (n + 2))
    (x : {x // x ∈ stdSimplex ℝ (Fin (n + 2))})
    (hx : x.val 0 ≠ 1) :
    let y := stdSimplex.faceMap (Fin.succ j) x
    let hy : y.val 0 ≠ 1 := by
      rw [stdSimplex.faceMap_val0 j x] ; exact hx
    stdSimplex.face0Proj (n + 1) y hy =
    stdSimplex.faceMap j (stdSimplex.face0Proj n x hx) := by
  let y := stdSimplex.faceMap (Fin.succ j) x
  have hy : y.val 0 ≠ 1 := by
    rw [stdSimplex.faceMap_val0 j x] ; exact hx
  dsimp only [y, hy]
  apply Subtype.ext
  funext m
  have h1 : (stdSimplex.face0Proj (n + 1) y hy).val m =
      y.val (Fin.succ m) / (1 - x.val 0) := by
    have h11 : y.val 0 = x.val 0 := stdSimplex.faceMap_val0 j x
    have h12 : 1 - y.val 0 = 1 - x.val 0 := by rw [h11]
    dsimp only [stdSimplex.face0Proj]
    rw [h12]
  have h2 : (stdSimplex.faceMap j (stdSimplex.face0Proj n x hx)).val m =
      (Finset.univ.filter (fun (y' : Fin (n + 1)) ↦ Fin.succAbove j y' = m)).sum
        (fun y' => (stdSimplex.face0Proj n x hx).val y') := by
    have h21 : (stdSimplex.faceMap j (stdSimplex.face0Proj n x hx)).val m =
        FunOnFinite.linearMap ℝ ℝ (Fin.succAbove j) (stdSimplex.face0Proj n x hx).val m := by
      simp [stdSimplex.faceMap] ; rfl
    rw [h21]
    exact FunOnFinite.linearMap_apply_apply ℝ ℝ j.succAbove (↑(face0Proj n x hx)) m
  have h3 : y.val (Fin.succ m) =
      (Finset.univ.filter (fun (z : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) z = Fin.succ m)).sum
        (fun z => x.val z) := by
    have h31 : y.val (Fin.succ m) =
        FunOnFinite.linearMap ℝ ℝ (Fin.succAbove (Fin.succ j)) x.val (Fin.succ m) := by
      simp [y, stdSimplex.faceMap] ; rfl
    rw [h31]
    exact FunOnFinite.linearMap_apply_apply ℝ ℝ j.succ.succAbove (↑x) m.succ
  have h4 : Finset.univ.filter (fun (z : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) z = Fin.succ m) =
      Finset.image Fin.succ (Finset.univ.filter (fun (y : Fin (n + 1)) ↦ Fin.succAbove j y = m)) :=
    fin_succAbove_comm j m
  have h5 : (Finset.univ.filter (fun (z : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) z = Fin.succ m)).sum
        (fun z => x.val z) =
      (Finset.univ.filter (fun (y' : Fin (n + 1)) ↦ Fin.succAbove j y' = m)).sum
        (fun y' => x.val (Fin.succ y')) := by
    rw [h4]
    rw [Finset.sum_image (fun x _ y _ h => by exact Fin.succ_inj.mp h)]
  have h6 : ∀ (y' : Fin (n + 1)), (stdSimplex.face0Proj n x hx).val y' =
      x.val (Fin.succ y') / (1 - x.val 0) := by
    intro y'
    rfl
  calc
    (stdSimplex.face0Proj (n + 1) y hy).val m
      = y.val (Fin.succ m) / (1 - x.val 0) := h1
    _ = ((Finset.univ.filter (fun (z : Fin (n + 2)) ↦ Fin.succAbove (Fin.succ j) z = Fin.succ m)).sum
          (fun z => x.val z)) / (1 - x.val 0) := by rw [h3]
    _ = ((Finset.univ.filter (fun (y' : Fin (n + 1)) ↦ Fin.succAbove j y' = m)).sum
          (fun y' => x.val (Fin.succ y'))) / (1 - x.val 0) := by rw [h5]
    _ = (Finset.univ.filter (fun (y' : Fin (n + 1)) ↦ Fin.succAbove j y' = m)).sum
          (fun y' => x.val (Fin.succ y') / (1 - x.val 0)) := by
      have h_sum_div : ∀ (s : Finset (Fin (n + 1))) (f : Fin (n + 1) → ℝ) (c : ℝ),
          s.sum f / c = s.sum (fun i => f i / c) := by
        intro s f c
        simp [div_eq_mul_inv, Finset.sum_mul]
      exact h_sum_div _ _ _
    _ = (Finset.univ.filter (fun (y' : Fin (n + 1)) ↦ Fin.succAbove j y' = m)).sum
          (fun y' => (stdSimplex.face0Proj n x hx).val y') := by
      apply Finset.sum_congr rfl
      intro y' _
      exact (h6 y').symm
    _ = (stdSimplex.faceMap j (stdSimplex.face0Proj n x hx)).val m := h2.symm

/-- Face i (for i > 0) of the cone `b * σ` is `b * (face_{i-1} σ)`.
Here `σ` is an (n+1)-simplex, and `j : Fin (n + 2)` indexes the face of σ. -/
theorem singularCone_face_succ {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {n : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (n + 2))} → E}
    (j : Fin (n + 2))
    (x : {x // x ∈ stdSimplex ℝ (Fin (n + 2))}) :
    singularCone (b := b) σ (stdSimplex.faceMap (Fin.succ j) x) =
    singularCone (b := b) (σ ∘ stdSimplex.faceMap j) x := by
  have h_val0 : (stdSimplex.faceMap (Fin.succ j) x).val 0 = x.val 0 :=
    stdSimplex.faceMap_val0 j x
  by_cases h_t0 : x.val 0 = 1
  · -- Case x.val 0 = 1: both sides equal b
    have h_t0' : (stdSimplex.faceMap (Fin.succ j) x).val 0 = 1 := by
      rw [h_val0, h_t0]
    dsimp only [singularCone]
    rw [dif_pos h_t0', dif_pos h_t0]
  · -- Case x.val 0 ≠ 1: both sides equal the affine combination
    have h_t0' : (stdSimplex.faceMap (Fin.succ j) x).val 0 ≠ 1 := by
      rw [h_val0] ; exact h_t0
    dsimp only [singularCone]
    rw [dif_neg h_t0', dif_neg h_t0]
    have h_comm : stdSimplex.face0Proj (n + 1) (stdSimplex.faceMap (Fin.succ j) x) h_t0' =
        stdSimplex.faceMap j (stdSimplex.face0Proj n x h_t0) :=
      stdSimplex.face0Proj_comm_faceMap j x h_t0
    have h_main : (stdSimplex.faceMap (Fin.succ j) x).val 0 • b +
        (1 - (stdSimplex.faceMap (Fin.succ j) x).val 0) •
          σ (stdSimplex.face0Proj (n + 1) (stdSimplex.faceMap (Fin.succ j) x) h_t0') =
        x.val 0 • b + (1 - x.val 0) • (σ ∘ stdSimplex.faceMap j) (stdSimplex.face0Proj n x h_t0) := by
      rw [h_val0, h_comm]
      ; rfl
    exact h_main

/-! ### Singular chains and chain-level cone -/

/-- The type of singular n-simplices in a topological space X. -/
def SingularSimplex (X : Type*) [TopologicalSpace X] (n : ℕ) :=
  { σ : ({x // x ∈ stdSimplex ℝ (Fin (n + 1))} → X) // Continuous σ }

/-- The type of singular n-chains with coefficients in R. -/
abbrev SingularChain (R : Type*) [Ring R] (X : Type*) [TopologicalSpace X] (n : ℕ) :=
  Finsupp (SingularSimplex X n) R

namespace SingularChain

variable {R : Type*} [Ring R] {X : Type*} [TopologicalSpace X]

/-- The i-th face of a singular simplex. -/
def face {n : ℕ} (i : Fin (n + 2)) (σ : SingularSimplex X (n + 1)) :
    SingularSimplex X n :=
  ⟨σ.val ∘ stdSimplex.faceMap i, σ.2.comp (stdSimplex.continuous_faceMap i)⟩

/-- The boundary map from (n+1)-chains to n-chains. -/
def d (n : ℕ) (c : SingularChain R X (n + 1)) : SingularChain R X n :=
  c.sum fun σ r => r • (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R))

lemma d_add (n : ℕ) (c1 c2 : SingularChain R X (n + 1)) :
    d n (c1 + c2) = d n c1 + d n c2 := by
  let h : SingularSimplex X (n + 1) → R →+ SingularChain R X n := fun σ =>
    { toFun := fun r => r • (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R))
      map_zero' := by simp
      map_add' := by intro r s; simp [add_smul]  }
  exact Finsupp.sum_hom_add_index h

lemma d_smul (n : ℕ) (r : R) (c : SingularChain R X (n + 1)) :
    d n (r • c) = r • d n c := by
  let f : SingularSimplex X (n + 1) → SingularChain R X n := fun σ =>
    ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R)
  have h0 : ∀ (σ : SingularSimplex X (n + 1)),
      (fun s : R => s • f σ) 0 = 0 := by
    intro σ; simp
  have h1 : d n (r • c) = (r • c).sum fun σ s => s • f σ := by rfl
  have h2 : d n c = c.sum fun σ s => s • f σ := by rfl
  rw [h1, h2]
  have h3 : (r • c).sum (fun σ s => s • f σ) = c.sum (fun σ s => (r * s) • f σ) := by
    exact Finsupp.sum_smul_index h0
  rw [h3]
  have h4 : c.sum (fun σ s => (r * s) • f σ) = c.sum (fun σ s => r • (s • f σ)) := by
    apply Finsupp.sum_congr
    intro σ _
    have h5 : ∀ (s : R), (r * s) • f σ = r • (s • f σ) := by
      intro s
      rw [smul_smul]
    exact h5 (c σ)
  rw [h4]
  have h5 : c.sum (fun σ s => r • (s • f σ)) = r • c.sum (fun σ s => s • f σ) := by
    have h_sum : c.sum (fun σ s => r • (s • f σ)) = ∑ σ ∈ Finsupp.support c, r • ((c σ) • f σ) := by
      rfl
    rw [h_sum]
    have h_smul : (∑ σ ∈ Finsupp.support c, r • ((c σ) • f σ)) = r • ∑ σ ∈ Finsupp.support c, (c σ) • f σ := by
      rw [←Finset.smul_sum]
    rw [h_smul]
    ; rfl
  exact h5

  /-! ### d∘d = 0 -/

  /-- If i.val < p.val, then (p.succAbove i).val = i.val -/
  lemma succAbove_val_lt {n : ℕ} {p : Fin (n + 1)} {i : Fin n} (h : i.val < p.val) :
      (p.succAbove i).val = i.val := by
    have h' : i.castSucc < p := by exact Fin.castSucc_lt_iff_succ_le.mpr h
    rw [Fin.succAbove_of_castSucc_lt p i h'] ; simp

  /-- If p.val ≤ i.val, then (p.succAbove i).val = i.val + 1 -/
  lemma succAbove_val_ge {n : ℕ} {p : Fin (n + 1)} {i : Fin n} (h : p.val ≤ i.val) :
      (p.succAbove i).val = i.val + 1 := by
    have h' : p ≤ i.castSucc := by exact Fin.le_def.mpr h
    rw [Fin.succAbove_of_le_castSucc p i h'] ; simp

  /-- The key Fin.succAbove identity for the simplicial identity. -/
  lemma fin_succAbove_simplicial {n : ℕ}
      {i : Fin (n + 3)} {j : Fin (n + 2)} (h : i ≤ Fin.castSucc j) :
      ∀ (k : Fin (n + 1)),
        (Fin.succAbove j.succ (Fin.succAbove (Fin.castLT i (by
          have h' : i.val < n + 2 := by
            have h1 : i ≤ Fin.castSucc j := h
            have h2 : (Fin.castSucc j).val = j.val := by simp
            rw [Fin.le_iff_val_le_val] at h1
            rw [h2] at h1
            have h3 : j.val < n + 2 := j.is_lt
            linarith
          exact h')) k)).val =
        (Fin.succAbove i (Fin.succAbove j k)).val := by
    let i' : Fin (n + 2) := Fin.castLT i (by
      have h' : i.val < n + 2 := by
        have h1 : i ≤ Fin.castSucc j := h
        have h2 : (Fin.castSucc j).val = j.val := by simp
        rw [Fin.le_iff_val_le_val] at h1
        rw [h2] at h1
        have h3 : j.val < n + 2 := j.is_lt
        linarith
      exact h')
    have hi'_val : i'.val = i.val := by simp [i']
    have h_ij : i.val ≤ j.val := by
      have h1 : i ≤ Fin.castSucc j := h
      have h2 : (Fin.castSucc j).val = j.val := by simp
      rw [Fin.le_iff_val_le_val] at h1
      rw [h2] at h1; exact h1
    intro k
    by_cases h1 : k.val < i.val
    · -- Case 1: k.val < i.val ≤ j.val
      have h2 : k.val < j.val := by linarith
      have h31 : (i'.succAbove k).val = k.val := succAbove_val_lt (by rw [hi'_val] ; exact h1)
      have h32 : (i'.succAbove k).val < (j.succ).val := by
        rw [h31] ; simp ; linarith
      have h4 : (j.succ.succAbove (i'.succAbove k)).val = (i'.succAbove k).val :=
        succAbove_val_lt h32
      have h_left : (j.succ.succAbove (i'.succAbove k)).val = k.val := by
        rw [h4, h31]
      have h51 : (j.succAbove k).val = k.val := succAbove_val_lt h2
      have h52 : (j.succAbove k).val < i.val := by
        rw [h51] ; exact h1
      have h6 : (i.succAbove (j.succAbove k)).val = (j.succAbove k).val :=
        succAbove_val_lt h52
      have h_right : (i.succAbove (j.succAbove k)).val = k.val := by
        rw [h6, h51]
      rw [h_left, h_right]
    · -- Case 2: i.val ≤ k.val
      have h1' : i.val ≤ k.val := by omega
      by_cases h2 : k.val < j.val
      · -- Subcase 2a: i.val ≤ k.val < j.val
        have h31 : (i'.succAbove k).val = k.val + 1 :=
          succAbove_val_ge (by rw [hi'_val] ; exact h1')
        have h32 : (i'.succAbove k).val < (j.succ).val := by
          rw [h31] ; simp ; linarith
        have h4 : (j.succ.succAbove (i'.succAbove k)).val = (i'.succAbove k).val :=
          succAbove_val_lt h32
        have h_left : (j.succ.succAbove (i'.succAbove k)).val = k.val + 1 := by
          rw [h4, h31]
        have h51 : (j.succAbove k).val = k.val := succAbove_val_lt h2
        have h52 : i.val ≤ (j.succAbove k).val := by
          rw [h51] ; exact h1'
        have h6 : (i.succAbove (j.succAbove k)).val = (j.succAbove k).val + 1 :=
          succAbove_val_ge h52
        have h_right : (i.succAbove (j.succAbove k)).val = k.val + 1 := by
          rw [h6, h51]
        rw [h_left, h_right]
      · -- Subcase 2b: j.val ≤ k.val
        have h2' : j.val ≤ k.val := by omega
        have h31 : (i'.succAbove k).val = k.val + 1 :=
          succAbove_val_ge (by rw [hi'_val] ; exact h1')
        have h32 : (j.succ).val ≤ (i'.succAbove k).val := by
          rw [h31] ; simp ; linarith
        have h4 : (j.succ.succAbove (i'.succAbove k)).val = (i'.succAbove k).val + 1 :=
          succAbove_val_ge h32
        have h_left : (j.succ.succAbove (i'.succAbove k)).val = k.val + 2 := by
          rw [h4, h31]
        have h51 : (j.succAbove k).val = k.val + 1 := succAbove_val_ge h2'
        have h52 : i.val ≤ (j.succAbove k).val := by
          rw [h51] ; linarith
        have h6 : (i.succAbove (j.succAbove k)).val = (j.succAbove k).val + 1 :=
          succAbove_val_ge h52
        have h_right : (i.succAbove (j.succAbove k)).val = k.val + 2 := by
          rw [h6, h51]
        rw [h_left, h_right]

  /-- Simplicial identity: for i ≤ j,
    `face i' (face j.succ σ) = face j (face i σ)`
    where i' is i cast down. -/
  lemma face_comp_face {n : ℕ} (σ : SingularSimplex X (n + 2))
      {i : Fin (n + 3)} {j : Fin (n + 2)} (h : i ≤ Fin.castSucc j) :
      face (Fin.castLT i (by
        have h' : i.val < n + 2 := by
          have h1 : i ≤ Fin.castSucc j := h
          have h2 : (Fin.castSucc j).val = j.val := by simp
          rw [Fin.le_iff_val_le_val] at h1
          rw [h2] at h1
          have h3 : j.val < n + 2 := j.is_lt
          linarith
        exact h')) (face j.succ σ) =
      face j (face i σ) := by
    let i' : Fin (n + 2) := Fin.castLT i (by
      have h' : i.val < n + 2 := by
        have h1 : i ≤ Fin.castSucc j := h
        have h2 : (Fin.castSucc j).val = j.val := by simp
        rw [Fin.le_iff_val_le_val] at h1
        rw [h2] at h1
        have h3 : j.val < n + 2 := j.is_lt
        linarith
      exact h')
    have h_fin : ∀ (k : Fin (n + 1)),
        (Fin.succAbove j.succ (Fin.succAbove i' k)).val = (Fin.succAbove i (Fin.succAbove j k)).val :=
      fin_succAbove_simplicial h
    have h_fin' : ∀ (k : Fin (n + 1)),
        Fin.succAbove j.succ (Fin.succAbove i' k) = Fin.succAbove i (Fin.succAbove j k) := by
      intro k
      apply Fin.ext
      exact h_fin k
    have h_comp : (fun k : Fin (n + 1) => Fin.succAbove j.succ (Fin.succAbove i' k)) =
        (fun k : Fin (n + 1) => Fin.succAbove i (Fin.succAbove j k)) := by
      funext k
      exact h_fin' k
    apply Subtype.ext
    funext x
    simp only [face, Function.comp_apply, Subtype.coe_mk, stdSimplex.faceMap]
    have h_eq1 : stdSimplex.map (Fin.succAbove j.succ) (stdSimplex.map (Fin.succAbove i') x) =
        stdSimplex.map (fun k : Fin (n + 1) => Fin.succAbove j.succ (Fin.succAbove i' k)) x := by
      rw [stdSimplex.map_comp_apply] ; rfl
    have h_eq2 : stdSimplex.map (Fin.succAbove i) (stdSimplex.map (Fin.succAbove j) x) =
        stdSimplex.map (fun k : Fin (n + 1) => Fin.succAbove i (Fin.succAbove j k)) x := by
      rw [stdSimplex.map_comp_apply] ; rfl
    rw [h_eq1, h_eq2]
    rw [h_comp]

  /-- The involution on pairs (i,j) that swaps the two orders of removing two vertices. -/
  def d_squared_involution (n : ℕ) :
      Fin (n + 3) × Fin (n + 2) → Fin (n + 3) × Fin (n + 2) :=
    fun p =>
      let i := p.1
      let j := p.2
      if h : j.val < i.val then
        (⟨j.val, by omega⟩, ⟨i.val - 1, by omega⟩)
      else
        (⟨j.val + 1, by omega⟩, ⟨i.val, by omega⟩)

  /-- The involution is indeed an involution. -/
  lemma d_squared_involution_invol (n : ℕ) :
      ∀ (p : Fin (n + 3) × Fin (n + 2)),
        d_squared_involution n (d_squared_involution n p) = p := by
    intro p
    let i := p.1
    let j := p.2
    have hi : i.val < n + 3 := i.is_lt
    have hj : j.val < n + 2 := j.is_lt
    dsimp only [d_squared_involution]
    by_cases h : j.val < i.val
    · rw [dif_pos h]
      let i2 : Fin (n + 3) := ⟨j.val, by omega⟩
      let j2 : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      have h2 : ¬ (j2.val < i2.val) := by
        dsimp only [i2, j2] ; omega
      rw [dif_neg h2]
      apply Prod.ext
      · apply Fin.ext
        dsimp only [i2, j2]
        have h_pos : 0 < i.val := by omega
        omega
      · apply Fin.ext
        dsimp only [i2, j2]
    · have h' : i.val ≤ j.val := by omega
      rw [dif_neg h]
      let i2 : Fin (n + 3) := ⟨j.val + 1, by omega⟩
      let j2 : Fin (n + 2) := ⟨i.val, by omega⟩
      have h2 : j2.val < i2.val := by
        dsimp only [i2, j2] ; omega
      rw [dif_pos h2]
      apply Prod.ext
      · apply Fin.ext
        dsimp only [i2, j2]
      · apply Fin.ext
        dsimp only [i2, j2] ; rfl

  /-- The involution has no fixed points. -/
  lemma d_squared_involution_no_fixed (n : ℕ) :
      ∀ (p : Fin (n + 3) × Fin (n + 2)),
        d_squared_involution n p ≠ p := by
    intro p
    let i := p.1
    let j := p.2
    have hi : i.val < n + 3 := i.is_lt
    have hj : j.val < n + 2 := j.is_lt
    dsimp only [d_squared_involution]
    by_cases h : j.val < i.val
    · rw [dif_pos h]
      intro h_eq
      have h_eq1 : (⟨j.val, by omega⟩ : Fin (n + 3)).val = i.val := by
        exact congr_arg (fun (x : Fin (n + 3) × Fin (n + 2)) => x.1.val) h_eq
      have h1 : j.val = i.val := by simpa using h_eq1
      omega
    · rw [dif_neg h]
      intro h_eq
      have h_eq1 : (⟨j.val + 1, by omega⟩ : Fin (n + 3)).val = i.val := by
        exact congr_arg (fun (x : Fin (n + 3) × Fin (n + 2)) => x.1.val) h_eq
      have h1 : j.val + 1 = i.val := by simpa using h_eq1
      omega

  /-- The sign flips under the involution. -/
  lemma d_squared_involution_sign_flip (n : ℕ) :
      ∀ (p : Fin (n + 3) × Fin (n + 2)),
        (-1 : R) ^ ((d_squared_involution n p).1.val + (d_squared_involution n p).2.val) =
        -((-1 : R) ^ (p.1.val + p.2.val)) := by
    intro p
    let i := p.1
    let j := p.2
    have hi : i.val < n + 3 := i.is_lt
    have hj : j.val < n + 2 := j.is_lt
    dsimp only [d_squared_involution]
    by_cases h : j.val < i.val
    · rw [dif_pos h]
      have h_pos : 0 < i.val + j.val := by omega
      have h_exp : j.val + (i.val - 1) + 1 = i.val + j.val := by omega
      have h_main : (-1 : R) ^ (j.val + (i.val - 1)) = -((-1 : R) ^ (i.val + j.val)) := by
        have h9 : (-1 : R) ^ (j.val + (i.val - 1) + 1) = (-1 : R) ^ (i.val + j.val) := by rw [h_exp]
        have h10 : (-1 : R) ^ (j.val + (i.val - 1) + 1) =
            (-1 : R) ^ (j.val + (i.val - 1)) * (-1 : R) := by
          rw [pow_succ]
        have h11 : (-1 : R) ^ (j.val + (i.val - 1)) * (-1 : R) = (-1 : R) ^ (i.val + j.val) := by
          rw [←h10, h9]
        have h_neg1_sq : (-1 : R) * (-1 : R) = 1 := by simp [mul_neg]
        have h12 : (-1 : R) ^ (j.val + (i.val - 1)) =
            (-1 : R) ^ (j.val + (i.val - 1)) * ((-1 : R) * (-1 : R)) := by
          rw [h_neg1_sq, mul_one]
        rw [h12, ←mul_assoc, h11] ; simp [mul_neg]
      have h_final : (-1 : R) ^ (j.val + (i.val - 1)) = -((-1 : R) ^ (p.1.val + p.2.val)) := by
        have h_eq : i.val + j.val = p.1.val + p.2.val := by simp [i, j]
        rw [h_main, h_eq]
      exact h_final
    · have h' : i.val ≤ j.val := by omega
      rw [dif_neg h]
      have h_exp : (j.val + 1) + i.val = (i.val + j.val) + 1 := by omega
      have h_goal : (-1 : R) ^ ((j.val + 1) + i.val) = (-1 : R) ^ (i.val + j.val) * (-1 : R) := by
        rw [h_exp, pow_succ]
      have h_final1 : (-1 : R) ^ ((j.val + 1) + i.val) = -((-1 : R) ^ (i.val + j.val)) := by
        rw [h_goal] ; simp [mul_neg]
      have h_eq : i.val + j.val = p.1.val + p.2.val := by simp [i, j]
      rw [h_final1, h_eq]

  /-- The resulting simplex is the same under the involution. -/
  lemma d_squared_involution_simplex_eq (n : ℕ) (σ : SingularSimplex X (n + 2)) :
      ∀ (p : Fin (n + 3) × Fin (n + 2)),
        face (d_squared_involution n p).2 (face (d_squared_involution n p).1 σ) =
        face p.2 (face p.1 σ) := by
    intro p
    let i := p.1
    let j := p.2
    have hi : i.val < n + 3 := i.is_lt
    have hj : j.val < n + 2 := j.is_lt
    dsimp only [d_squared_involution]
    by_cases h : j.val < i.val
    · rw [dif_pos h]
      let i2 : Fin (n + 3) := ⟨j.val, by omega⟩
      let j2 : Fin (n + 2) := ⟨i.val - 1, by omega⟩
      have h_le : i2 ≤ Fin.castSucc j2 := by
        dsimp only [i2, j2]
        simp [Fin.le_iff_val_le_val] ; omega
      have h_face : face (Fin.castLT i2 (by omega)) (face j2.succ σ) = face j2 (face i2 σ) :=
        face_comp_face σ h_le
      have h_i2_cast : (Fin.castLT i2 (by omega)) = j := by
        apply Fin.ext
        simp [i2]
      have h_j2_succ : j2.succ = i := by
        apply Fin.ext
        simp [j2] ; omega
      rw [h_i2_cast, h_j2_succ] at h_face
      exact h_face.symm
    · have h' : i.val ≤ j.val := by omega
      rw [dif_neg h]
      have h_le : i ≤ Fin.castSucc j := by
        simp [Fin.le_iff_val_le_val] ; omega
      have h_face : face (Fin.castLT i (by omega)) (face j.succ σ) = face j (face i σ) :=
        face_comp_face σ h_le
      convert h_face <;> apply Fin.ext <;> simp <;> omega

  /-- For a single simplex σ, d(d(single σ 1)) = 0. -/
  lemma d_squared_single (n : ℕ) (σ : SingularSimplex X (n + 2)) :
      d n (d (n + 1) (Finsupp.single σ (1 : R))) = 0 := by
    let g := d_squared_involution n
    have h_invol : ∀ (p : Fin (n + 3) × Fin (n + 2)), g (g p) = p :=
      d_squared_involution_invol n
    have h_no_fixed : ∀ (p : Fin (n + 3) × Fin (n + 2)), g p ≠ p :=
      d_squared_involution_no_fixed n
    have h_sign : ∀ (p : Fin (n + 3) × Fin (n + 2)),
        (-1 : R) ^ ((g p).1.val + (g p).2.val) = -((-1 : R) ^ (p.1.val + p.2.val)) :=
      d_squared_involution_sign_flip n
    have h_simplex : ∀ (p : Fin (n + 3) × Fin (n + 2)),
        face (g p).2 (face (g p).1 σ) = face p.2 (face p.1 σ) :=
      d_squared_involution_simplex_eq n σ
    let f : Fin (n + 3) × Fin (n + 2) → SingularChain R X n := fun p =>
      (-1 : R) ^ (p.1.val + p.2.val) • Finsupp.single (face p.2 (face p.1 σ)) (1 : R)
    have h_cancel : ∀ (p : Fin (n + 3) × Fin (n + 2)), f p + f (g p) = 0 := by
      intro p
      dsimp only [f]
      rw [h_sign p, h_simplex p] ; simp [neg_smul]
    have h_main : ∑ p : Fin (n + 3) × Fin (n + 2), f p = 0 := by
      exact Finset.sum_ninvolution g
        (fun p => h_cancel p)
        (fun p _ => h_no_fixed p)
        (fun p => Finset.mem_univ (g p))
        (fun p => h_invol p)
    have h1 : d (n + 1) (Finsupp.single σ (1 : R)) =
        ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R) := by
      dsimp only [d]
      rw [Finsupp.sum_single_index (by simp)] ; simp [one_smul]
    let d_n_hom : SingularChain R X (n + 1) →+ SingularChain R X n :=
      { toFun := d n
        map_zero' := by simp [d]
        map_add' := d_add n }
    have h_d_sum : ∀ (s : Finset (Fin (n + 3))) (f : Fin (n + 3) → SingularChain R X (n + 1)),
        d n (∑ i ∈ s, f i) = ∑ i ∈ s, d n (f i) := by
      intro s f
      exact map_sum d_n_hom f s
    have h_d_smul_sum : ∀ (s : Finset (Fin (n + 3))) (c : Fin (n + 3) → R)
        (f : Fin (n + 3) → SingularChain R X (n + 1)),
        d n (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • d n (f i) := by
      intro s c f
      rw [h_d_sum s (fun i => c i • f i)]
      apply Finset.sum_congr rfl
      intro i _
      exact d_smul n (c i) (f i)
    have h2 : d n (d (n + 1) (Finsupp.single σ (1 : R))) =
        ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) •
          d n (Finsupp.single (face i σ) (1 : R)) := by
      rw [h1]
      exact h_d_smul_sum Finset.univ (fun i => (-1 : R) ^ (i : ℕ))
        (fun i => Finsupp.single (face i σ) (1 : R))
    rw [h2]
    have h3 : ∀ (i : Fin (n + 3)),
        d n (Finsupp.single (face i σ) (1 : R)) =
        ∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • Finsupp.single (face j (face i σ)) (1 : R) := by
      intro i
      dsimp only [d]
      rw [Finsupp.sum_single_index (by simp)] ; simp [one_smul]
    have h4 : ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) • d n (Finsupp.single (face i σ) (1 : R)) =
        ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) •
          (∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • Finsupp.single (face j (face i σ)) (1 : R)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h3 i]
    rw [h4]
    have h5 : ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) •
          (∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • Finsupp.single (face j (face i σ)) (1 : R)) =
        ∑ p : Fin (n + 3) × Fin (n + 2), f p := by
      have h51 : ∀ (i : Fin (n + 3)),
          (-1 : R) ^ (i : ℕ) •
            (∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • Finsupp.single (face j (face i σ)) (1 : R)) =
          ∑ j : Fin (n + 2),
            ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) •
              Finsupp.single (face j (face i σ)) (1 : R) := by
        intro i
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
      have h52 : ∑ i : Fin (n + 3), (-1 : R) ^ (i : ℕ) •
            (∑ j : Fin (n + 2), (-1 : R) ^ (j : ℕ) • Finsupp.single (face j (face i σ)) (1 : R)) =
          ∑ i : Fin (n + 3), ∑ j : Fin (n + 2),
            ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) •
              Finsupp.single (face j (face i σ)) (1 : R) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h51 i
      rw [h52]
      let g : Fin (n + 3) → Fin (n + 2) → SingularChain R X n := fun i j =>
        ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) •
          Finsupp.single (face j (face i σ)) (1 : R)
      have h53 : ∑ i : Fin (n + 3), ∑ j : Fin (n + 2), g i j =
          ∑ p : Fin (n + 3) × Fin (n + 2), g p.1 p.2 := by exact Eq.symm (Fintype.sum_prod_type' g)
      rw [h53]
      apply Finset.sum_congr rfl
      intro p _
      dsimp only [f, g]
      have h_exp : (-1 : R) ^ (p.1.val + p.2.val) = (-1 : R) ^ (p.1 : ℕ) * (-1 : R) ^ (p.2 : ℕ) := by
        rw [←pow_add]
      rw [h_exp]
    rw [h5, h_main]

  /-- The boundary of a boundary is zero: `d n (d (n + 1) c) = 0`. -/
  lemma d_squared (n : ℕ) (c : SingularChain R X (n + 2)) :
      d n (d (n + 1) c) = 0 := by
    let P : SingularChain R X (n + 2) → Prop := fun c' => d n (d (n + 1) c') = 0
    have h_zero : P 0 := by simp [P, d]
    have h_add : ∀ (σ : SingularSimplex X (n + 2)) (r : R) (c' : SingularChain R X (n + 2)),
        σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
      intro σ r c' _ _ ih
      dsimp only [P] at *
      have h1 : d (n + 1) (Finsupp.single σ r + c') = d (n + 1) (Finsupp.single σ r) + d (n + 1) c' :=
        d_add (n + 1) (Finsupp.single σ r) c'
      rw [h1]
      have h2 : d n (d (n + 1) (Finsupp.single σ r) + d (n + 1) c') =
          d n (d (n + 1) (Finsupp.single σ r)) + d n (d (n + 1) c') := d_add n _ _
      rw [h2, ih]
      have h3 : d (n + 1) (Finsupp.single σ r) = r • d (n + 1) (Finsupp.single σ (1 : R)) := by
        have h4 : Finsupp.single σ r = r • Finsupp.single σ (1 : R) := by
          simp [Finsupp.smul_single]
        rw [h4]
        exact d_smul (n + 1) r (Finsupp.single σ (1 : R))
      rw [h3]
      have h5 : d n (r • d (n + 1) (Finsupp.single σ (1 : R))) =
          r • d n (d (n + 1) (Finsupp.single σ (1 : R))) :=
        d_smul n r (d (n + 1) (Finsupp.single σ (1 : R)))
      rw [h5]
      rw [d_squared_single n σ] ; simp
    have h_main : ∀ (c : SingularChain R X (n + 2)), P c := fun c =>
      Finsupp.induction c h_zero h_add
    exact h_main c

end SingularChain

/-! ### Chain-level cone construction -/

namespace singularCone

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {b : E} {k : ℕ} (hs : Convex ℝ s) (hb : b ∈ s)

/-- The cone of a singular simplex (as a `SingularSimplex` in `s`).
Here `σ` is a (k+1)-simplex and the cone is a (k+2)-simplex. -/
def coneSimplex (σ : SingularSimplex s (k + 1)) : SingularSimplex s (k + 2) :=
  let σ_E : {x // x ∈ stdSimplex ℝ (Fin (k + 2))} → E := fun t => (σ.val t).val
  have hσ_E_cont : Continuous σ_E := continuous_subtype_val.comp σ.2
  have hσ_E_in : ∀ t, σ_E t ∈ s := fun t => (σ.val t).property
  let cone_E : {x // x ∈ stdSimplex ℝ (Fin (k + 2 + 1))} → E :=
    singularCone (b := b) σ_E
  have h_cone_cont : Continuous cone_E := singularCone_continuous hσ_E_cont
  have h_cone_mem : ∀ t, cone_E t ∈ s := singularCone_mem hs hb σ_E hσ_E_in
  let f : {x // x ∈ stdSimplex ℝ (Fin (k + 2 + 1))} → s :=
    fun t => ⟨cone_E t, h_cone_mem t⟩
  have h_f_cont : Continuous f := by
    exact Continuous.subtype_mk h_cone_cont h_cone_mem
  ⟨f, h_f_cont⟩

end singularCone

/-- The cone of a singular simplex (as a `SingularSimplex` in `s`).
Takes an n-simplex to an (n+1)-simplex. -/
def singularConeSimplex {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s) {n : ℕ}
    (σ : SingularSimplex s n) : SingularSimplex s (n + 1) :=
  let σ_E : {x // x ∈ stdSimplex ℝ (Fin (n + 1))} → E := fun t => (σ.val t).val
  have hσ_E_cont : Continuous σ_E := continuous_subtype_val.comp σ.2
  have hσ_E_in : ∀ t, σ_E t ∈ s := fun t => (σ.val t).property
  let cone_E : {x // x ∈ stdSimplex ℝ (Fin (n + 1 + 1))} → E :=
    singularCone (b := b) σ_E
  have h_cone_cont : Continuous cone_E := singularCone_continuous hσ_E_cont
  have h_cone_mem : ∀ t, cone_E t ∈ s := singularCone_mem hs hb σ_E hσ_E_in
  let f : {x // x ∈ stdSimplex ℝ (Fin (n + 1 + 1))} → s :=
    fun t => ⟨cone_E t, h_cone_mem t⟩
  have h_f_cont : Continuous f := by
    exact Continuous.subtype_mk h_cone_cont h_cone_mem
  ⟨f, h_f_cont⟩

/-- The cone map on chains: linear extension of the cone on simplices.
Takes n-chains to (n+1)-chains. -/
def singularConeMap {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s) (n : ℕ)
    (c : SingularChain ℤ s n) : SingularChain ℤ s (n + 1) :=
  c.sum fun σ r => r • Finsupp.single (singularConeSimplex hs hb σ) (1 : ℤ)

lemma singularConeMap_add {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s) (n : ℕ)
    (c1 c2 : SingularChain ℤ s n) :
    singularConeMap hs hb n (c1 + c2) = singularConeMap hs hb n c1 + singularConeMap hs hb n c2 := by
  let h : SingularSimplex s n → ℤ →+ SingularChain ℤ s (n + 1) := fun σ =>
    { toFun := fun r => r • Finsupp.single (singularConeSimplex hs hb σ) (1 : ℤ)
      map_zero' := by simp
      map_add' := by intro r s; simp [add_smul]  }
  exact Finsupp.sum_hom_add_index h

lemma singularConeMap_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s) (n : ℕ)
    (r : ℤ) (c : SingularChain ℤ s n) :
    singularConeMap hs hb n (r • c) = r • singularConeMap hs hb n c := by
  let f : SingularSimplex s n → SingularChain ℤ s (n + 1) := fun σ =>
    Finsupp.single (singularConeSimplex hs hb σ) (1 : ℤ)
  have h0 : ∀ (σ : SingularSimplex s n),
      (fun s : ℤ => s • f σ) 0 = 0 := by
    intro σ; simp
  have h1 : singularConeMap hs hb n (r • c) = (r • c).sum fun σ s => s • f σ := by rfl
  have h2 : singularConeMap hs hb n c = c.sum fun σ s => s • f σ := by rfl
  rw [h1, h2]
  have h3 : (r • c).sum (fun σ s => s • f σ) = c.sum (fun σ s => (r * s) • f σ) := by
    exact Finsupp.sum_smul_index h0
  rw [h3]
  have h4 : c.sum (fun σ s => (r * s) • f σ) = c.sum (fun σ s => r • (s • f σ)) := by
    apply Finsupp.sum_congr
    intro σ _
    have h5 : ∀ (s : ℤ), (r * s) • f σ = r • (s • f σ) := by
      intro s
      rw [smul_smul]
    exact h5 (c σ)
  rw [h4]
  have h5 : c.sum (fun σ s => r • (s • f σ)) = r • c.sum (fun σ s => s • f σ) := by
    have h_sum : c.sum (fun σ s => r • (s • f σ)) = ∑ σ ∈ Finsupp.support c, r • ((c σ) • f σ) := by rfl
    rw [h_sum]
    have h_smul : (∑ σ ∈ Finsupp.support c, r • ((c σ) • f σ)) = r • ∑ σ ∈ Finsupp.support c, (c σ) • f σ := by
      rw [←Finset.smul_sum]
    rw [h_smul]
    ; rfl
  exact h5

/-- The cone boundary formula on chains: `d(cone(b, c)) = c - cone(b, d(c))`.
Holds for all n ≥ 0 (with d(c) = 0 when n = 0). -/
theorem singularCone.d_cone_eq {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s) (n : ℕ)
    (c : SingularChain ℤ s (n + 1)) :
    SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c) =
    c - singularConeMap hs hb n (SingularChain.d n c) := by
  have hσ_E_in : ∀ (σ : SingularSimplex s (n + 1)) (t : {x // x ∈ stdSimplex ℝ (Fin (n + 2))}),
      (fun t : {x // x ∈ stdSimplex ℝ (Fin (n + 2))} => (σ.val t).val) t ∈ s :=
    fun σ t => (σ.val t).property
  -- Face 0 of cone is σ
  have h_face0 : ∀ (σ : SingularSimplex s (n + 1)),
      SingularChain.face (0 : Fin (n + 3)) (singularConeSimplex hs hb σ) = σ := by
    intro σ
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact singularCone_face0 (b := b) (σ := fun t => (σ.val t).val) x
  -- Face j+1 of cone is cone of face j
  have h_face_succ : ∀ (σ : SingularSimplex s (n + 1)) (j : Fin (n + 2)),
      SingularChain.face (Fin.succ j) (singularConeSimplex hs hb σ) =
      singularConeSimplex hs hb (SingularChain.face j σ) := by
    intro σ j
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact singularCone_face_succ (b := b) (σ := fun t => (σ.val t).val) j x
  -- Helper: coneMap of a finite sum of smul singles
  have h_cone_sum : ∀ (σ : SingularSimplex s (n + 1)),
      singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (singularConeSimplex hs hb (SingularChain.face j σ)) (1 : ℤ) := by
    intro σ
    have h_d1 : SingularChain.d n (Finsupp.single σ (1 : ℤ)) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (SingularChain.face j σ) (1 : ℤ) := by
      simp [SingularChain.d, Finsupp.sum_single_index]
    rw [h_d1]
    have h_sum : singularConeMap hs hb n (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (SingularChain.face j σ) (1 : ℤ)) =
        ∑ j : Fin (n + 2), singularConeMap hs hb n ((-1 : ℤ) ^ (j : ℕ) • Finsupp.single (SingularChain.face j σ) (1 : ℤ)) := by
      let F : SingularChain ℤ s n →+ SingularChain ℤ s (n + 1) :=
        { toFun := fun c => singularConeMap hs hb n c
          map_zero' := by simp [singularConeMap]
          map_add' := fun x y => singularConeMap_add hs hb n x y }
      exact map_sum F (fun j : Fin (n + 2) => (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (SingularChain.face j σ) (1 : ℤ)) Finset.univ
    rw [h_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [singularConeMap_smul hs hb n ((-1 : ℤ) ^ (j : ℕ)) (Finsupp.single (SingularChain.face j σ) (1 : ℤ))]
    ; simp [singularConeMap, Finsupp.sum_single_index]
  -- Formula for a single simplex with coefficient 1
  have h_single1 : ∀ (σ : SingularSimplex s (n + 1)),
      SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ (1 : ℤ))) +
      singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
      Finsupp.single σ (1 : ℤ) := by
    intro σ
    have h1 : SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ (1 : ℤ))) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (SingularChain.face i (singularConeSimplex hs hb σ)) (1 : ℤ) := by
      simp [SingularChain.d, singularConeMap, Finsupp.sum_single_index]
    rw [h1, h_cone_sum σ]
    have h3 : (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (SingularChain.face i (singularConeSimplex hs hb σ)) (1 : ℤ)) =
        (-1 : ℤ) ^ (0 : ℕ) • Finsupp.single (SingularChain.face (0 : Fin (n + 3)) (singularConeSimplex hs hb σ)) (1 : ℤ) +
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (Fin.succ j : ℕ) • Finsupp.single (SingularChain.face (Fin.succ j) (singularConeSimplex hs hb σ)) (1 : ℤ) := by
      rw [Fin.sum_univ_succ] ; rfl
    rw [h3]
    rw [h_face0 σ]
    have h4 : (∑ j : Fin (n + 2), (-1 : ℤ) ^ (Fin.succ j : ℕ) • Finsupp.single (SingularChain.face (Fin.succ j) (singularConeSimplex hs hb σ)) (1 : ℤ)) =
        (-1 : ℤ) • (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (singularConeSimplex hs hb (SingularChain.face j σ)) (1 : ℤ)) := by
      have h5 : ∀ (j : Fin (n + 2)), (-1 : ℤ) ^ (Fin.succ j : ℕ) • Finsupp.single (SingularChain.face (Fin.succ j) (singularConeSimplex hs hb σ)) (1 : ℤ) =
          (-1 : ℤ) • ((-1 : ℤ) ^ (j : ℕ) • Finsupp.single (singularConeSimplex hs hb (SingularChain.face j σ)) (1 : ℤ)) := by
        intro j
        rw [h_face_succ σ j]
        ; simp [pow_succ]
      calc
        (∑ j : Fin (n + 2), (-1 : ℤ) ^ (Fin.succ j : ℕ) • Finsupp.single (SingularChain.face (Fin.succ j) (singularConeSimplex hs hb σ)) (1 : ℤ))
          = ∑ j : Fin (n + 2), (-1 : ℤ) • ((-1 : ℤ) ^ (j : ℕ) • Finsupp.single (singularConeSimplex hs hb (SingularChain.face j σ)) (1 : ℤ)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact h5 j
        _ = (-1 : ℤ) • (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (singularConeSimplex hs hb (SingularChain.face j σ)) (1 : ℤ)) := by
          rw [Finset.smul_sum]
    rw [h4]
    ; simp [one_smul]
  -- Induction on c
  let P : SingularChain ℤ s (n + 1) → Prop := fun c' =>
    SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c') +
      singularConeMap hs hb n (SingularChain.d n c') = c'
  have h_zero : P 0 := by
    simp [P, SingularChain.d, singularConeMap]
  have h_add : ∀ (σ : SingularSimplex s (n + 1)) (r : ℤ) (c' : SingularChain ℤ s (n + 1)),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : singularConeMap hs hb (n + 1) (Finsupp.single σ r + c') =
        singularConeMap hs hb (n + 1) (Finsupp.single σ r) + singularConeMap hs hb (n + 1) c' :=
      singularConeMap_add hs hb (n + 1) (Finsupp.single σ r) c'
    have h2 : SingularChain.d n (Finsupp.single σ r + c') =
        SingularChain.d n (Finsupp.single σ r) + SingularChain.d n c' :=
      SingularChain.d_add n (Finsupp.single σ r) c'
    have h_single_r : SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ r)) +
        singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ r)) = Finsupp.single σ r := by
      have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
        simp [Finsupp.smul_single]
      rw [hsr]
      rw [singularConeMap_smul hs hb (n + 1) r (Finsupp.single σ (1 : ℤ))]
      rw [SingularChain.d_smul (n + 1) r (singularConeMap hs hb (n + 1) (Finsupp.single σ (1 : ℤ)))]
      rw [SingularChain.d_smul n r (Finsupp.single σ (1 : ℤ))]
      rw [singularConeMap_smul hs hb n r (SingularChain.d n (Finsupp.single σ (1 : ℤ)))]
      have h := h_single1 σ
      have h' : r • (SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ (1 : ℤ))) +
          singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ (1 : ℤ)))) =
          r • Finsupp.single σ (1 : ℤ) := by
        rw [h]
      simpa [smul_add, Finsupp.smul_single] using h'
    calc
      SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ r + c')) +
        singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ r + c'))
        = SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ r) + singularConeMap hs hb (n + 1) c') +
            singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ r) + SingularChain.d n c') := by rw [h1, h2]
      _ = SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ r)) +
            SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c') +
            singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ r)) +
            singularConeMap hs hb n (SingularChain.d n c') := by
          rw [SingularChain.d_add (n + 1) _ _, singularConeMap_add hs hb n _ _]
          ; abel
      _ = (SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) (Finsupp.single σ r)) +
            singularConeMap hs hb n (SingularChain.d n (Finsupp.single σ r))) +
          (SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c') +
            singularConeMap hs hb n (SingularChain.d n c')) := by abel
      _ = Finsupp.single σ r + c' := by rw [h_single_r, ih]
  have hP : P c := Finsupp.induction c h_zero h_add
  have h' : SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c) +
      singularConeMap hs hb n (SingularChain.d n c) = c := hP
  have h_final : SingularChain.d (n + 1) (singularConeMap hs hb (n + 1) c) =
      c - singularConeMap hs hb n (SingularChain.d n c) := by
    exact eq_sub_of_add_eq h'
  exact h_final

/-!
# Barycentric Subdivision and Chain Homotopy

Building on the cone construction and cone boundary formula,
we define barycentric subdivision sd and the chain homotopy T
with dT + Td = sd - id.
-/

-- ============================================
-- Pushforward of singular chains
-- ============================================

namespace SingularChain

variable {R : Type*} [Ring R] {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pushforward of a singular simplex along a continuous map. -/
def pushforwardSimplex (f : C(X, Y)) {n : ℕ} (σ : SingularSimplex X n) :
    SingularSimplex Y n :=
  ⟨f ∘ σ.val, f.continuous.comp σ.2⟩

/-- Pushforward of singular chains along a continuous map. -/
def pushforward (f : C(X, Y)) {n : ℕ} (c : SingularChain R X n) :
    SingularChain R Y n :=
  c.sum fun σ r => r • Finsupp.single (pushforwardSimplex f σ) (1 : R)

lemma pushforward_add (f : C(X, Y)) {n : ℕ} (c1 c2 : SingularChain R X n) :
    pushforward f (c1 + c2) = pushforward f c1 + pushforward f c2 := by
  let h : SingularSimplex X n → R →+ SingularChain R Y n := fun σ =>
    { toFun := fun r => r • Finsupp.single (pushforwardSimplex f σ) (1 : R)
      map_zero' := by simp
      map_add' := by intro r s; simp [add_smul]  }
  exact Finsupp.sum_hom_add_index h

lemma pushforward_smul (f : C(X, Y)) {n : ℕ} (r : R) (c : SingularChain R X n) :
    pushforward f (r • c) = r • pushforward f c := by
  let g : SingularSimplex X n → SingularChain R Y n := fun σ =>
    Finsupp.single (pushforwardSimplex f σ) (1 : R)
  have h0 : ∀ (σ : SingularSimplex X n), (fun s : R => s • g σ) 0 = 0 := by
    intro σ; simp
  have h1 : pushforward f (r • c) = (r • c).sum fun σ s => s • g σ := by rfl
  have h2 : pushforward f c = c.sum fun σ s => s • g σ := by rfl
  rw [h1, h2]
  have h3 : (r • c).sum (fun σ s => s • g σ) = c.sum (fun σ s => (r * s) • g σ) := by
    exact Finsupp.sum_smul_index h0
  rw [h3]
  have h4 : c.sum (fun σ s => (r * s) • g σ) = c.sum (fun σ s => r • (s • g σ)) := by
    apply Finsupp.sum_congr
    intro σ _
    have h5 : ∀ (s : R), (r * s) • g σ = r • (s • g σ) := by
      intro s; rw [smul_smul]
    exact h5 (c σ)
  rw [h4]
  have h5 : c.sum (fun σ s => r • (s • g σ)) = r • c.sum (fun σ s => s • g σ) := by
    have h_sum : c.sum (fun σ s => r • (s • g σ)) = ∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ) := by rfl
    rw [h_sum]
    have h_smul : (∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ)) = r • ∑ σ ∈ Finsupp.support c, (c σ) • g σ := by
      rw [←Finset.smul_sum]
    rw [h_smul] ; rfl
  exact h5

/-- Pushforward commutes with the boundary map (naturality). -/
lemma pushforward_d (f : C(X, Y)) {n : ℕ} (c : SingularChain R X (n + 1)) :
    pushforward f (d n c) = d n (pushforward f c) := by
  have h_face : ∀ (i : Fin (n + 2)) (σ : SingularSimplex X (n + 1)),
      pushforwardSimplex f (face i σ) = face i (pushforwardSimplex f σ) := by
    intro i σ
    apply Subtype.ext
    funext x
    rfl
  let P : SingularChain R X (n + 1) → Prop := fun c' =>
    pushforward f (d n c') = d n (pushforward f c')
  have h_zero : P 0 := by
    simp [P, d, pushforward]
  have h_add : ∀ (σ : SingularSimplex X (n + 1)) (r : R) (c' : SingularChain R X (n + 1)),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : d n (Finsupp.single σ r + c') = d n (Finsupp.single σ r) + d n c' := d_add n (Finsupp.single σ r) c'
    have h2 : pushforward f (Finsupp.single σ r + c') = pushforward f (Finsupp.single σ r) + pushforward f c' :=
      pushforward_add f (Finsupp.single σ r) c'
    rw [h1, pushforward_add f (d n (Finsupp.single σ r)) (d n c'), h2, d_add n (pushforward f (Finsupp.single σ r)) (pushforward f c')]
    rw [ih]
    congr 1
    -- Now prove for single simplex with coefficient r
    have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : R) := by
      simp [Finsupp.smul_single]
    rw [hsr]
    rw [pushforward_smul f r (Finsupp.single σ (1 : R)), d_smul n r (pushforward f (Finsupp.single σ (1 : R)))]
    rw [d_smul n r (Finsupp.single σ (1 : R)), pushforward_smul f r (d n (Finsupp.single σ (1 : R)))]
    congr 1
    -- Now prove for single simplex with coefficient 1
    have h_single1 :
        pushforward f (d n (Finsupp.single σ (1 : R))) =
        d n (pushforward f (Finsupp.single σ (1 : R))) := by
      have h_d1 : d n (Finsupp.single σ (1 : R)) =
          ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R) := by
        simp [d, Finsupp.sum_single_index]
      have h_d2 : d n (pushforward f (Finsupp.single σ (1 : R))) =
          ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i (pushforwardSimplex f σ)) (1 : R) := by
        simp [d, pushforward, pushforwardSimplex, Finsupp.sum_single_index]
      rw [h_d1, h_d2]
      have h_sum1 : pushforward f (∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R)) =
          ∑ i : Fin (n + 2), pushforward f ((-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R)) := by
        let F : SingularChain R X n →+ SingularChain R Y n :=
          { toFun := fun c => pushforward f c
            map_zero' := by simp [pushforward]
            map_add' := fun x y => pushforward_add f x y }
        exact map_sum F (fun i : Fin (n + 2) => (-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R)) Finset.univ
      rw [h_sum1]
      apply Finset.sum_congr rfl
      intro i _
      have h_smul : pushforward f ((-1 : R) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : R)) =
          (-1 : R) ^ (i : ℕ) • pushforward f (Finsupp.single (face i σ) (1 : R)) :=
        pushforward_smul f ((-1 : R) ^ (i : ℕ)) (Finsupp.single (face i σ) (1 : R))
      rw [h_smul]
      have h_face' : pushforwardSimplex f (face i σ) = face i (pushforwardSimplex f σ) := h_face i σ
      have h_eq : pushforward f (Finsupp.single (face i σ) (1 : R)) =
          Finsupp.single (face i (pushforwardSimplex f σ)) (1 : R) := by
        simp [pushforward, pushforwardSimplex, Finsupp.sum_single_index]
        ; rfl
      rw [h_eq]
    exact h_single1
  exact Finsupp.induction c h_zero h_add

  -- ============================================
  -- Small chains (𝒰-small)
  -- ============================================

  /-- A singular simplex σ is 𝒰-small if its image is contained in some U ∈ 𝒰. -/
  def IsSmallWithRespectTo {X : Type*} [TopologicalSpace X] {ι : Type*}
      (𝒰 : ι → Set X) {n : ℕ} (σ : SingularSimplex X n) : Prop :=
    ∃ (i : ι), Set.range σ.val ⊆ 𝒰 i

  /-- A chain is 𝒰-small if every simplex in its support is 𝒰-small. -/
  def AllSmall {X : Type*} [TopologicalSpace X] {ι : Type*}
      (𝒰 : ι → Set X) {n : ℕ} (c : SingularChain ℤ X n) : Prop :=
    ∀ σ ∈ Finsupp.support c, IsSmallWithRespectTo 𝒰 σ

  /-- The zero chain is 𝒰-small. -/
  lemma allSmall_zero {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} :
      AllSmall 𝒰 (0 : SingularChain ℤ X n) := by
    intro σ hσ
    simp at hσ

  /-- Sum of two 𝒰-small chains is 𝒰-small. -/
  lemma allSmall_add {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {c1 c2 : SingularChain ℤ X n}
      (h1 : AllSmall 𝒰 c1) (h2 : AllSmall 𝒰 c2) :
      AllSmall 𝒰 (c1 + c2) := by
    intro σ hσ
    have h3 : (c1 + c2) σ ≠ 0 := Finsupp.mem_support_iff.mp hσ
    have h4 : c1 σ ≠ 0 ∨ c2 σ ≠ 0 := by
      by_contra h5
      push Not at h5
      have h6 : (c1 + c2) σ = 0 := by
        rw [Finsupp.add_apply, h5.1, h5.2] ; simp
      exact h3 h6
    cases h4 with
    | inl h4 =>
      have h5 : σ ∈ Finsupp.support c1 := Finsupp.mem_support_iff.mpr h4
      exact h1 σ h5
    | inr h4 =>
      have h5 : σ ∈ Finsupp.support c2 := Finsupp.mem_support_iff.mpr h4
      exact h2 σ h5

  /-- A single simplex chain is 𝒰-small if the simplex is 𝒰-small. -/
  lemma allSmall_single {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {σ : SingularSimplex X n} {r : ℤ}
      (h : IsSmallWithRespectTo 𝒰 σ) : AllSmall 𝒰 (Finsupp.single σ r) := by
    intro τ hτ
    have h5 : τ = σ ∧ r ≠ 0 := (Finsupp.mem_support_single τ σ r).mp hτ
    rw [h5.1]
    exact h

  /-- Finite sum of 𝒰-small chains is 𝒰-small. -/
  lemma allSmall_sum {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {α : Type*} {s : Finset α}
      {f : α → SingularChain ℤ X n} (h : ∀ i ∈ s, AllSmall 𝒰 (f i)) :
      AllSmall 𝒰 (∑ i ∈ s, f i) := by
    classical
    induction s using Finset.induction with
    | empty =>
      simpa using allSmall_zero
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact allSmall_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

  /-- Scalar multiple of a 𝒰-small chain is 𝒰-small. -/
  lemma allSmall_smul {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {c : SingularChain ℤ X n} {a : ℤ}
      (h : AllSmall 𝒰 c) : AllSmall 𝒰 (a • c) := by
    intro σ hσ
    have h3 : (a • c) σ ≠ 0 := Finsupp.mem_support_iff.mp hσ
    have h4 : a * c σ ≠ 0 := by
      have h_eq : (a • c) σ = a * c σ := by
        rw [Finsupp.smul_apply]
        ; rfl
      rw [h_eq] at h3
      exact h3
    have h5 : c σ ≠ 0 := (mul_ne_zero_iff.mp h4).2
    have h6 : σ ∈ Finsupp.support c := Finsupp.mem_support_iff.mpr h5
    exact h σ h6

  /-- Negation of a 𝒰-small chain is 𝒰-small. -/
  lemma allSmall_neg {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {c : SingularChain ℤ X n}
      (h : AllSmall 𝒰 c) : AllSmall 𝒰 (-c) := by
    have h' : AllSmall 𝒰 ((-1 : ℤ) • c) := allSmall_smul h
    simpa [neg_one_smul] using h'

  /-- Difference of two 𝒰-small chains is 𝒰-small. -/
  lemma allSmall_sub {X : Type*} [TopologicalSpace X] {ι : Type*}
      {𝒰 : ι → Set X} {n : ℕ} {c1 c2 : SingularChain ℤ X n}
      (h1 : AllSmall 𝒰 c1) (h2 : AllSmall 𝒰 c2) :
      AllSmall 𝒰 (c1 - c2) := by
    have h : c1 - c2 = c1 + (-c2) := by
      ext x; simp [sub_eq_add_neg]
    rw [h]
    exact allSmall_add h1 (allSmall_neg h2)

end SingularChain

-- ============================================
-- Barycenter of standard simplex
-- ============================================

namespace stdSimplex

/-- The barycenter (center of mass) of the standard n-simplex. -/
def barycenter (n : ℕ) : {x // x ∈ stdSimplex ℝ (Fin (n + 1))} :=
  let f : Fin (n + 1) → ℝ := fun _ => (1 : ℝ) / (n + 1 : ℝ)
  have h_nonneg : ∀ i : Fin (n + 1), 0 ≤ f i := by
    intro i; positivity
  have h_sum1 : ∑ i : Fin (n + 1), f i = 1 := by
    dsimp only [f]
    have h1 : ∑ i : Fin (n + 1), (1 : ℝ) / (n + 1 : ℝ) =
        (Finset.card (Finset.univ : Finset (Fin (n + 1))) : ℝ) * ((1 : ℝ) / (n + 1 : ℝ)) := by
      rw [Finset.sum_const] ; ring
    rw [h1]
    have h2 : (Finset.card (Finset.univ : Finset (Fin (n + 1))) : ℝ) = (n + 1 : ℝ) := by
      simp
    rw [h2]
    have h_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    field_simp
  ⟨f, ⟨h_nonneg, h_sum1⟩⟩

end stdSimplex

-- ============================================
-- Barycentric subdivision - fundamental class
-- ============================================

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

/-- The fundamental singular n-simplex on the standard simplex (identity map). -/
def fundamentalSimplex (n : ℕ) :
    SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n :=
  ⟨fun x => x, continuous_id⟩

/-- The fundamental chain: the fundamental simplex with coefficient 1. -/
def fundamentalChain (n : ℕ) :
    SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n :=
  Finsupp.single (fundamentalSimplex n) (1 : ℤ)

/-- Barycentric subdivision of the fundamental simplex.
Inductive definition: sd(ι₀) = ι₀, sd(ι_{n+1}) = b * sd(∂ι_{n+1}). -/
def sd_fundamental (n : ℕ) :
    SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n :=
  Nat.casesOn n
    (fundamentalChain 0)
    (fun k =>
      let X := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
      let b : X := stdSimplex.barycenter (k + 1)
      let hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))) := by exact convex_stdSimplex ℝ (Fin (k + 2))
      let dι : SingularChain ℤ X k := SingularChain.d k (fundamentalChain (k + 1))
      let sd_dι : SingularChain ℤ X k :=
        dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental k)
      singularConeMap hs b.property k sd_dι)

-- ============================================
-- Barycentric subdivision on arbitrary simplices/chains
-- ============================================

/-- Barycentric subdivision of a singular simplex:
sd(σ) := σ_*(sd_fundamental) - pushforward of the fundamental subdivision. -/
def sdSimplex {X : Type*} [TopologicalSpace X] {n : ℕ}
    (σ : SingularSimplex X n) : SingularChain ℤ X n :=
  SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n)

/-- Barycentric subdivision on chains: linear extension of sdSimplex. -/
def sdMap {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c : SingularChain ℤ X n) : SingularChain ℤ X n :=
  c.sum fun σ r => r • sdSimplex σ

lemma sdMap_add {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c1 c2 : SingularChain ℤ X n) :
    sdMap n (c1 + c2) = sdMap n c1 + sdMap n c2 := by
  let h : SingularSimplex X n → ℤ →+ SingularChain ℤ X n := fun σ =>
    { toFun := fun r => r • sdSimplex σ
      map_zero' := by simp
      map_add' := by intro r s; simp [add_smul]  }
  exact Finsupp.sum_hom_add_index h

lemma sdMap_smul {X : Type*} [TopologicalSpace X] (n : ℕ)
    (r : ℤ) (c : SingularChain ℤ X n) :
    sdMap n (r • c) = r • sdMap n c := by
  let g : SingularSimplex X n → SingularChain ℤ X n := fun σ => sdSimplex σ
  have h0 : ∀ (σ : SingularSimplex X n), (fun s : ℤ => s • g σ) 0 = 0 := by
    intro σ; simp
  have h1 : sdMap n (r • c) = (r • c).sum fun σ s => s • g σ := by rfl
  have h2 : sdMap n c = c.sum fun σ s => s • g σ := by rfl
  rw [h1, h2]
  have h3 : (r • c).sum (fun σ s => s • g σ) = c.sum (fun σ s => (r * s) • g σ) := by
    exact Finsupp.sum_smul_index h0
  rw [h3]
  have h4 : c.sum (fun σ s => (r * s) • g σ) = c.sum (fun σ s => r • (s • g σ)) := by
    apply Finsupp.sum_congr
    intro σ _
    have h5 : ∀ (s : ℤ), (r * s) • g σ = r • (s • g σ) := by
      intro s; rw [smul_smul]
    exact h5 (c σ)
  rw [h4]
  have h5 : c.sum (fun σ s => r • (s • g σ)) = r • c.sum (fun σ s => s • g σ) := by
    have h_sum : c.sum (fun σ s => r • (s • g σ)) = ∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ) := by rfl
    rw [h_sum]
    have h_smul : (∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ)) = r • ∑ σ ∈ Finsupp.support c, (c σ) • g σ := by
      rw [←Finset.smul_sum]
    rw [h_smul] ; rfl
  exact h5

-- ============================================
-- sd commutes with pushforward
-- ============================================

/-- Pushforward is functorial: (f ∘ g)_* = f_* ∘ g_* on simplices. -/
lemma SingularChain.pushforwardSimplex_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(X, Y)) {n : ℕ} (σ : SingularSimplex X n) :
    pushforwardSimplex (f.comp g) σ = pushforwardSimplex f (pushforwardSimplex g σ) := by
  apply Subtype.ext
  funext x
  ; rfl

/-- Pushforward is functorial: (f ∘ g)_* = f_* ∘ g_* on chains. -/
lemma SingularChain.pushforward_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (g : C(X, Y)) {n : ℕ} (c : SingularChain ℤ X n) :
    pushforward (f.comp g) c = pushforward f (pushforward g c) := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    pushforward (f.comp g) c' = pushforward f (pushforward g c')
  have h_zero : P 0 := by
    simp [P, pushforward]
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : pushforward (f.comp g) (Finsupp.single σ r + c') =
        pushforward (f.comp g) (Finsupp.single σ r) + pushforward (f.comp g) c' :=
      pushforward_add (f.comp g) (Finsupp.single σ r) c'
    have h2 : pushforward g (Finsupp.single σ r + c') =
        pushforward g (Finsupp.single σ r) + pushforward g c' :=
      pushforward_add g (Finsupp.single σ r) c'
    rw [h1, h2, pushforward_add f (pushforward g (Finsupp.single σ r)) (pushforward g c'), ih]
    congr 1
    have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
      simp [Finsupp.smul_single]
    rw [hsr]
    rw [pushforward_smul (f.comp g) r (Finsupp.single σ (1 : ℤ))]
    rw [pushforward_smul g r (Finsupp.single σ (1 : ℤ))]
    rw [pushforward_smul f r (pushforward g (Finsupp.single σ (1 : ℤ)))]
    congr 1
    simp [pushforward, pushforwardSimplex_comp f g σ, Finsupp.sum_single_index]
  exact Finsupp.induction c h_zero h_add

/-- sd commutes with pushforward on simplices. -/
lemma sdSimplex_pushforward {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (σ : SingularSimplex X n) :
    sdSimplex (SingularChain.pushforwardSimplex f σ) =
    SingularChain.pushforward f (sdSimplex σ) := by
  dsimp only [sdSimplex]
  have h : SingularChain.pushforward ⟨(f ∘ σ.val), f.continuous.comp σ.2⟩ (sd_fundamental n) =
      SingularChain.pushforward f (SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n)) :=
    SingularChain.pushforward_comp f ⟨σ.val, σ.2⟩ (sd_fundamental n)
  exact h

/-- sd commutes with pushforward on chains. -/
lemma sdMap_pushforward {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (c : SingularChain ℤ X n) :
    sdMap n (SingularChain.pushforward f c) =
    SingularChain.pushforward f (sdMap n c) := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    sdMap n (SingularChain.pushforward f c') = SingularChain.pushforward f (sdMap n c')
  have h_zero : P 0 := by
    simp [P, sdMap, SingularChain.pushforward]
  have h_single : ∀ (σ : SingularSimplex X n) (r : ℤ),
      P (Finsupp.single σ r) := by
    intro σ r
    dsimp only [P]
    have h1 : sdMap n (SingularChain.pushforward f (Finsupp.single σ r)) =
        r • sdMap n (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ))) := by
      have h1a : SingularChain.pushforward f (Finsupp.single σ r) =
          r • SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)) := by
        rw [show Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) from by
          simp [Finsupp.smul_single] ]
        exact SingularChain.pushforward_smul f r (Finsupp.single σ (1 : ℤ))
      rw [h1a]
      exact sdMap_smul n r (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)))
    have h2 : SingularChain.pushforward f (sdMap n (Finsupp.single σ r)) =
        r • SingularChain.pushforward f (sdMap n (Finsupp.single σ (1 : ℤ))) := by
      have h2a : sdMap n (Finsupp.single σ r) = r • sdMap n (Finsupp.single σ (1 : ℤ)) := by
        rw [show Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) from by
          simp [Finsupp.smul_single] ]
        exact sdMap_smul n r (Finsupp.single σ (1 : ℤ))
      rw [h2a]
      exact SingularChain.pushforward_smul f r (sdMap n (Finsupp.single σ (1 : ℤ)))
    rw [h1, h2]
    congr 1
    have h3 : sdMap n (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ))) =
        sdSimplex (SingularChain.pushforwardSimplex f σ) := by
      have h31 : SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)) =
          Finsupp.single (SingularChain.pushforwardSimplex f σ) (1 : ℤ) := by
        simp [SingularChain.pushforward, SingularChain.pushforwardSimplex, Finsupp.sum_single_index]
      rw [h31]
      simp [sdMap, Finsupp.sum_single_index]
    have h4 : SingularChain.pushforward f (sdMap n (Finsupp.single σ (1 : ℤ))) =
        SingularChain.pushforward f (sdSimplex σ) := by
      have h41 : sdMap n (Finsupp.single σ (1 : ℤ)) = sdSimplex σ := by
        simp [sdMap, Finsupp.sum_single_index]
      rw [h41]
    rw [h3, h4]
    exact sdSimplex_pushforward f σ
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : sdMap n (SingularChain.pushforward f (Finsupp.single σ r + c')) =
        sdMap n (SingularChain.pushforward f (Finsupp.single σ r)) + sdMap n (SingularChain.pushforward f c') := by
      have h1a : SingularChain.pushforward f (Finsupp.single σ r + c') =
          SingularChain.pushforward f (Finsupp.single σ r) + SingularChain.pushforward f c' :=
        SingularChain.pushforward_add f (Finsupp.single σ r) c'
      rw [h1a]
      exact sdMap_add n (SingularChain.pushforward f (Finsupp.single σ r)) (SingularChain.pushforward f c')
    have h2 : SingularChain.pushforward f (sdMap n (Finsupp.single σ r + c')) =
        SingularChain.pushforward f (sdMap n (Finsupp.single σ r)) + SingularChain.pushforward f (sdMap n c') := by
      have h2a : sdMap n (Finsupp.single σ r + c') = sdMap n (Finsupp.single σ r) + sdMap n c' :=
        sdMap_add n (Finsupp.single σ r) c'
      rw [h2a]
      exact SingularChain.pushforward_add f (sdMap n (Finsupp.single σ r)) (sdMap n c')
    rw [h1, h2]
    have h3 : sdMap n (SingularChain.pushforward f (Finsupp.single σ r)) =
        SingularChain.pushforward f (sdMap n (Finsupp.single σ r)) := h_single σ r
    rw [h3, ih]
  exact Finsupp.induction c h_zero h_add

-- ============================================
-- sd is a chain map
-- ============================================

/-- Helper: from the fundamental chain map property at degree n,
deduce the chain map property for any (n+1)-simplex. -/
lemma sd_simplex_chainMap_of_fundamental (n : ℕ)
    (h_fund : SingularChain.d n (sd_fundamental (n + 1)) =
      sdMap n (SingularChain.d n (fundamentalChain (n + 1)))) :
    ∀ {X : Type*} [TopologicalSpace X] (σ : SingularSimplex X (n + 1)),
      SingularChain.d n (sdSimplex σ) =
      sdMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) := by
  intro X _ σ
  have h1 : SingularChain.d n (sdSimplex σ) =
      SingularChain.d n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1))) := by rfl
  rw [h1]
  have h2 : SingularChain.d n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1))) =
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (sd_fundamental (n + 1))) :=
    (SingularChain.pushforward_d ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1))).symm
  rw [h2]
  rw [h_fund]
  have h3 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (sdMap n (SingularChain.d n (fundamentalChain (n + 1)))) =
      sdMap n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1)))) :=
    (sdMap_pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1)))).symm
  rw [h3]
  have h4 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1))) =
      SingularChain.d n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1))) :=
    SingularChain.pushforward_d ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1))
  rw [h4]
  have h5 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) =
      Finsupp.single σ (1 : ℤ) := by
    simp [fundamentalChain, SingularChain.pushforward, SingularChain.pushforwardSimplex, Finsupp.sum_single_index]
    ; rfl
  rw [h5]

/-- sdMap is the identity on 0-chains. -/
lemma sdMap_zero_id {X : Type*} [TopologicalSpace X] (c : SingularChain ℤ X 0) :
    sdMap 0 c = c := by
  have h1 : ∀ (σ : SingularSimplex X 0), sdSimplex σ = Finsupp.single σ (1 : ℤ) := by
    intro σ
    dsimp only [sdSimplex, sd_fundamental, fundamentalChain]
    simp [SingularChain.pushforward, Finsupp.sum_single_index]
    ; rfl
  have h2 : sdMap 0 c = c.sum (fun σ r => r • Finsupp.single σ (1 : ℤ)) := by
    dsimp only [sdMap]
    congr
    ; funext σ
    ; rw [h1 σ]
  rw [h2]
  have h3 : c.sum (fun σ r => r • Finsupp.single σ (1 : ℤ)) = c := by
    apply Finsupp.ext
    intro σ
    simp
  rw [h3]

/-- Helper: for any 1-chain c, the boundary of the cone of its boundary is the boundary itself.
    Proof: apply d_cone_eq at degree 1, then use d_squared. -/
lemma d_cone_of_boundary {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {b : E} (hs : Convex ℝ s) (hb : b ∈ s)
    (c : SingularChain ℤ s 1) :
    SingularChain.d 0 (singularConeMap hs hb 0 (SingularChain.d 0 c)) =
    SingularChain.d 0 c := by
  let c' := singularConeMap hs hb 0 (SingularChain.d 0 c)
  have h_cone1 : SingularChain.d 1 (singularConeMap hs hb 1 c) = c - c' :=
    singularCone.d_cone_eq hs hb 0 c
  have h_d2 : SingularChain.d 0 (SingularChain.d 1 (singularConeMap hs hb 1 c)) = 0 :=
    SingularChain.d_squared 0 (singularConeMap hs hb 1 c)
  have h_d_add : SingularChain.d 0 (c - c') = SingularChain.d 0 c - SingularChain.d 0 c' := by
    have h1 : SingularChain.d 0 (c + (-c')) = SingularChain.d 0 c + SingularChain.d 0 (-c') :=
      SingularChain.d_add 0 c (-c')
    have h2 : SingularChain.d 0 (-c') = -SingularChain.d 0 c' := by
      have h3 : (-1 : ℤ) • c' = -c' := by simp
      rw [←h3, SingularChain.d_smul 0 (-1 : ℤ) c']
      ; simp
    have h4 : c - c' = c + (-c') := by
      exact SubNegMonoid.sub_eq_add_neg c c'
    rw [h4, h1, h2]
    ; abel
  have h5 : SingularChain.d 0 c - SingularChain.d 0 c' = 0 := by
    rw [←h_d_add, ←h_cone1]
    exact h_d2
  have h6 : SingularChain.d 0 c' = SingularChain.d 0 c := by
    exact sub_eq_zero.mp h5 |>.symm
  exact h6

/-- Helper: from the simplex-wise chain map property, deduce it for all chains. -/
lemma sd_chainMap_of_simplex {X : Type*} [TopologicalSpace X] (n : ℕ)
    (h_simplex : ∀ (σ : SingularSimplex X (n + 1)),
      SingularChain.d n (sdSimplex σ) =
      sdMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ)))) :
    ∀ (c : SingularChain ℤ X (n + 1)),
      SingularChain.d n (sdMap (n + 1) c) = sdMap n (SingularChain.d n c) := by
  let P : SingularChain ℤ X (n + 1) → Prop := fun c' =>
    SingularChain.d n (sdMap (n + 1) c') = sdMap n (SingularChain.d n c')
  have h_zero : P 0 := by
    simp [P, sdMap, SingularChain.d]
  have h_add : ∀ (σ : SingularSimplex X (n + 1)) (r : ℤ) (c' : SingularChain ℤ X (n + 1)),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : sdMap (n + 1) (Finsupp.single σ r + c') =
        sdMap (n + 1) (Finsupp.single σ r) + sdMap (n + 1) c' :=
      sdMap_add (n + 1) (Finsupp.single σ r) c'
    have h2 : SingularChain.d n (Finsupp.single σ r + c') =
        SingularChain.d n (Finsupp.single σ r) + SingularChain.d n c' :=
      SingularChain.d_add n (Finsupp.single σ r) c'
    rw [h1, h2]
    rw [SingularChain.d_add n (sdMap (n + 1) (Finsupp.single σ r)) (sdMap (n + 1) c')]
    rw [sdMap_add n (SingularChain.d n (Finsupp.single σ r)) (SingularChain.d n c')]
    rw [ih]
    congr 1
    have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
      simp [Finsupp.smul_single]
    rw [hsr]
    rw [sdMap_smul (n + 1) r (Finsupp.single σ (1 : ℤ))]
    rw [SingularChain.d_smul n r (sdMap (n + 1) (Finsupp.single σ (1 : ℤ)))]
    rw [SingularChain.d_smul n r (Finsupp.single σ (1 : ℤ))]
    rw [sdMap_smul n r (SingularChain.d n (Finsupp.single σ (1 : ℤ)))]
    congr 1
    simpa [sdMap, Finsupp.sum_single_index] using h_simplex σ
  intro c
  exact Finsupp.induction c h_zero h_add

/-- **sd is a chain map**: d(sd(c)) = sd(d(c)).
Proved by induction on n, simultaneously for the fundamental simplex
and for all chains (using naturality). -/
theorem sd_chainMap {X : Type*} [TopologicalSpace X] (n : ℕ) :
    ∀ (c : SingularChain ℤ X (n + 1)),
      SingularChain.d n (sdMap (n + 1) c) = sdMap n (SingularChain.d n c) := by
  -- First prove by induction on n that the fundamental case holds for all n
  have h_fund : ∀ n : ℕ,
      SingularChain.d n (sd_fundamental (n + 1)) =
      sdMap n (SingularChain.d n (fundamentalChain (n + 1))) := by
    intro n
    induction n with
    | zero =>
      -- Base case n = 0
      let X := {x // x ∈ stdSimplex ℝ (Fin 2)}
      let b : X := stdSimplex.barycenter 1
      let hs : Convex ℝ (stdSimplex ℝ (Fin 2)) := by exact convex_stdSimplex ℝ (Fin 2)
      let dι : SingularChain ℤ X 0 := SingularChain.d 0 (fundamentalChain 1)
      let sd_dι : SingularChain ℤ X 0 :=
        dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental 0)
      have h_def : sd_fundamental 1 = singularConeMap hs b.property 0 sd_dι := by
        dsimp only [sd_fundamental, Nat.casesOn] ; rfl
      have h_sd_dι_eq : sd_dι = sdMap 0 dι := by rfl
      have h_sd0_id' : sdMap 0 dι = dι := sdMap_zero_id dι
      have h_sd_dι_eq_dι : sd_dι = dι := by
        rw [h_sd_dι_eq, h_sd0_id']
      have h_main1 : SingularChain.d 0 (sd_fundamental 1) = dι := by
        rw [h_def, h_sd_dι_eq_dι]
        exact d_cone_of_boundary hs b.property (fundamentalChain 1)
      have h_main2 : sdMap 0 (SingularChain.d 0 (fundamentalChain 1)) = dι := by
        exact sdMap_zero_id dι
      rw [h_main1, h_main2]
    | succ n ih =>
      let X := {x // x ∈ stdSimplex ℝ (Fin (n + 3))}
      let b : X := stdSimplex.barycenter (n + 2)
      let hs : Convex ℝ (stdSimplex ℝ (Fin (n + 3))) := by exact convex_stdSimplex ℝ (Fin (n + 3))
      let dι : SingularChain ℤ X (n + 1) := SingularChain.d (n + 1) (fundamentalChain (n + 2))
      let sd_dι : SingularChain ℤ X (n + 1) :=
        dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1))
      have h_def : sd_fundamental (n + 2) = singularConeMap hs b.property (n + 1) sd_dι := by
        dsimp only [sd_fundamental, Nat.casesOn] ; rfl
      have h_goal : SingularChain.d (n + 1) (sd_fundamental (n + 2)) =
          sdMap (n + 1) (SingularChain.d (n + 1) (fundamentalChain (n + 2))) := by
        rw [h_def]
        have h_cone : SingularChain.d (n + 1) (singularConeMap hs b.property (n + 1) sd_dι) =
            sd_dι - singularConeMap hs b.property n (SingularChain.d n sd_dι) :=
          singularCone.d_cone_eq hs b.property n sd_dι
        rw [h_cone]
        have h_sd_dι_def : sd_dι = sdMap (n + 1) dι := by
          rfl
        rw [h_sd_dι_def]
        have h_chainMap_n : ∀ (c : SingularChain ℤ X (n + 1)),
            SingularChain.d n (sdMap (n + 1) c) = sdMap n (SingularChain.d n c) :=
          sd_chainMap_of_simplex (n := n)
            (sd_simplex_chainMap_of_fundamental n ih)
        have h_d_sd : SingularChain.d n (sdMap (n + 1) dι) =
            sdMap n (SingularChain.d n dι) := h_chainMap_n dι
        rw [h_d_sd]
        have h_dd : SingularChain.d n dι = 0 := by
          dsimp only [dι]
          exact SingularChain.d_squared n (fundamentalChain (n + 2))
        rw [h_dd]
        have h_sd0 : sdMap n (0 : SingularChain ℤ X n) = 0 := by
          simp [sdMap]
        rw [h_sd0]
        have h_cone0 : singularConeMap hs b.property n (0 : SingularChain ℤ X n) = 0 := by
          simp [singularConeMap]
        rw [h_cone0]
        ; abel
      exact h_goal
  exact sd_chainMap_of_simplex (n := n) (sd_simplex_chainMap_of_fundamental n (h_fund n))

-- Chain homotopy T
-- ============================================

/-- The chain homotopy operator on the fundamental simplex.
Inductive definition: T(ι₀) = 0, T(ι_{n+1}) = b * (sd(ι_n) - ι_n - T(d(ι_n))). -/
def T_fundamental (n : ℕ) :
    SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} (n + 1) :=
  Nat.casesOn n
    (0 : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (0 + 1))} (0 + 1))
    (fun k =>
      let X := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
      let b : X := stdSimplex.barycenter (k + 1)
      let hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))) := by exact convex_stdSimplex ℝ (Fin (k + 2))
      let dι : SingularChain ℤ X k := SingularChain.d k (fundamentalChain (k + 1))
      let sd_ι : SingularChain ℤ X (k + 1) := sd_fundamental (k + 1)
      let T_dι : SingularChain ℤ X (k + 1) :=
        dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental k)
      singularConeMap hs b.property (k + 1) (sd_ι - fundamentalChain (k + 1) - T_dι))

/-- Chain homotopy T applied to a singular simplex. -/
def TSimplex {X : Type*} [TopologicalSpace X] {n : ℕ}
    (σ : SingularSimplex X n) : SingularChain ℤ X (n + 1) :=
  SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental n)

/-- Chain homotopy T on chains: linear extension of TSimplex. -/
def TMap {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c : SingularChain ℤ X n) : SingularChain ℤ X (n + 1) :=
  c.sum fun σ r => r • TSimplex σ

lemma TMap_add {X : Type*} [TopologicalSpace X] (n : ℕ)
    (c1 c2 : SingularChain ℤ X n) :
    TMap n (c1 + c2) = TMap n c1 + TMap n c2 := by
  let h : SingularSimplex X n → ℤ →+ SingularChain ℤ X (n + 1) := fun σ =>
    { toFun := fun r => r • TSimplex σ
      map_zero' := by simp
      map_add' := by intro r s; simp [add_smul]  }
  exact Finsupp.sum_hom_add_index h

lemma TMap_smul {X : Type*} [TopologicalSpace X] (n : ℕ)
    (r : ℤ) (c : SingularChain ℤ X n) :
    TMap n (r • c) = r • TMap n c := by
  let g : SingularSimplex X n → SingularChain ℤ X (n + 1) := fun σ => TSimplex σ
  have h0 : ∀ (σ : SingularSimplex X n), (fun s : ℤ => s • g σ) 0 = 0 := by
    intro σ; simp
  have h1 : TMap n (r • c) = (r • c).sum fun σ s => s • g σ := by rfl
  have h2 : TMap n c = c.sum fun σ s => s • g σ := by rfl
  rw [h1, h2]
  have h3 : (r • c).sum (fun σ s => s • g σ) = c.sum (fun σ s => (r * s) • g σ) := by
    exact Finsupp.sum_smul_index h0
  rw [h3]
  have h4 : c.sum (fun σ s => (r * s) • g σ) = c.sum (fun σ s => r • (s • g σ)) := by
    apply Finsupp.sum_congr
    intro σ _
    have h5 : ∀ (s : ℤ), (r * s) • g σ = r • (s • g σ) := by
      intro s; rw [smul_smul]
    exact h5 (c σ)
  rw [h4]
  have h5 : c.sum (fun σ s => r • (s • g σ)) = r • c.sum (fun σ s => s • g σ) := by
    have h_sum : c.sum (fun σ s => r • (s • g σ)) = ∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ) := by rfl
    rw [h_sum]
    have h_smul : (∑ σ ∈ Finsupp.support c, r • ((c σ) • g σ)) = r • ∑ σ ∈ Finsupp.support c, (c σ) • g σ := by
      rw [←Finset.smul_sum]
    rw [h_smul] ; rfl
  exact h5

/-- T commutes with pushforward on simplices. -/
lemma TSimplex_pushforward {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (σ : SingularSimplex X n) :
    TSimplex (SingularChain.pushforwardSimplex f σ) =
    SingularChain.pushforward f (TSimplex σ) := by
  dsimp only [TSimplex]
  exact SingularChain.pushforward_comp f ⟨σ.val, σ.2⟩ (T_fundamental n)

/-- T commutes with pushforward on chains. -/
lemma TMap_pushforward {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {n : ℕ} (c : SingularChain ℤ X n) :
    TMap n (SingularChain.pushforward f c) =
    SingularChain.pushforward f (TMap n c) := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    TMap n (SingularChain.pushforward f c') = SingularChain.pushforward f (TMap n c')
  have h_zero : P 0 := by
    simp [P, TMap, SingularChain.pushforward]
  have h_single : ∀ (σ : SingularSimplex X n) (r : ℤ),
      P (Finsupp.single σ r) := by
    intro σ r
    dsimp only [P]
    have h1 : TMap n (SingularChain.pushforward f (Finsupp.single σ r)) =
        r • TMap n (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ))) := by
      have h1a : SingularChain.pushforward f (Finsupp.single σ r) =
          r • SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)) := by
        rw [show Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) from by
          simp [Finsupp.smul_single] ]
        exact SingularChain.pushforward_smul f r (Finsupp.single σ (1 : ℤ))
      rw [h1a]
      exact TMap_smul n r (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)))
    have h2 : SingularChain.pushforward f (TMap n (Finsupp.single σ r)) =
        r • SingularChain.pushforward f (TMap n (Finsupp.single σ (1 : ℤ))) := by
      have h2a : TMap n (Finsupp.single σ r) = r • TMap n (Finsupp.single σ (1 : ℤ)) := by
        rw [show Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) from by
          simp [Finsupp.smul_single] ]
        exact TMap_smul n r (Finsupp.single σ (1 : ℤ))
      rw [h2a]
      exact SingularChain.pushforward_smul f r (TMap n (Finsupp.single σ (1 : ℤ)))
    rw [h1, h2]
    congr 1
    have h3 : TMap n (SingularChain.pushforward f (Finsupp.single σ (1 : ℤ))) =
        TSimplex (SingularChain.pushforwardSimplex f σ) := by
      have h31 : SingularChain.pushforward f (Finsupp.single σ (1 : ℤ)) =
          Finsupp.single (SingularChain.pushforwardSimplex f σ) (1 : ℤ) := by
        simp [SingularChain.pushforward, SingularChain.pushforwardSimplex, Finsupp.sum_single_index]
      rw [h31]
      simp [TMap, Finsupp.sum_single_index]
    have h4 : SingularChain.pushforward f (TMap n (Finsupp.single σ (1 : ℤ))) =
        SingularChain.pushforward f (TSimplex σ) := by
      have h41 : TMap n (Finsupp.single σ (1 : ℤ)) = TSimplex σ := by
        simp [TMap, Finsupp.sum_single_index]
      rw [h41]
    rw [h3, h4]
    exact TSimplex_pushforward f σ
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : TMap n (SingularChain.pushforward f (Finsupp.single σ r + c')) =
        TMap n (SingularChain.pushforward f (Finsupp.single σ r)) + TMap n (SingularChain.pushforward f c') := by
      have h1a : SingularChain.pushforward f (Finsupp.single σ r + c') =
          SingularChain.pushforward f (Finsupp.single σ r) + SingularChain.pushforward f c' :=
        SingularChain.pushforward_add f (Finsupp.single σ r) c'
      rw [h1a]
      exact TMap_add n (SingularChain.pushforward f (Finsupp.single σ r)) (SingularChain.pushforward f c')
    have h2 : SingularChain.pushforward f (TMap n (Finsupp.single σ r + c')) =
        SingularChain.pushforward f (TMap n (Finsupp.single σ r)) + SingularChain.pushforward f (TMap n c') := by
      have h2a : TMap n (Finsupp.single σ r + c') = TMap n (Finsupp.single σ r) + TMap n c' :=
        TMap_add n (Finsupp.single σ r) c'
      rw [h2a]
      exact SingularChain.pushforward_add f (TMap n (Finsupp.single σ r)) (TMap n c')
    rw [h1, h2]
    have h3 : TMap n (SingularChain.pushforward f (Finsupp.single σ r)) =
        SingularChain.pushforward f (TMap n (Finsupp.single σ r)) := h_single σ r
    rw [h3, ih]
  exact Finsupp.induction c h_zero h_add

-- ============================================
-- Chain homotopy property
-- ============================================


/-- Helper: from the fundamental homotopy property at degree n,
deduce the homotopy property for any (n+1)-simplex. -/
lemma T_simplex_homotopy_of_fundamental (n : ℕ)
    (h_fund :
      SingularChain.d (n + 1) (T_fundamental (n + 1)) + TMap n (SingularChain.d n (fundamentalChain (n + 1))) =
      sd_fundamental (n + 1) - fundamentalChain (n + 1)) :
    ∀ {X : Type*} [TopologicalSpace X] (σ : SingularSimplex X (n + 1)),
      SingularChain.d (n + 1) (TSimplex σ) + TMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
      sdSimplex σ - Finsupp.single σ (1 : ℤ) := by
  intro X _ σ
  have h1 : SingularChain.d (n + 1) (TSimplex σ) =
      SingularChain.d (n + 1) (SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental (n + 1))) := by rfl
  have h2 : SingularChain.d (n + 1) (SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental (n + 1))) =
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d (n + 1) (T_fundamental (n + 1))) :=
    (SingularChain.pushforward_d ⟨σ.val, σ.2⟩ (T_fundamental (n + 1))).symm
  have h3 : TMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
      TMap n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1)))) := by
    have h31 : SingularChain.d n (Finsupp.single σ (1 : ℤ)) =
        SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1))) := by
      have h : SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) = Finsupp.single σ (1 : ℤ) := by
        simp [fundamentalChain, SingularChain.pushforward, SingularChain.pushforwardSimplex, Finsupp.sum_single_index]
        ; rfl
      have h' : SingularChain.d n (Finsupp.single σ (1 : ℤ)) =
          SingularChain.d n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1))) := by rw [h]
      rw [h']
      exact (SingularChain.pushforward_d ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1))).symm
    rw [h31]
  rw [h1, h2, h3]
  have h4 : TMap n (SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1)))) =
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (TMap n (SingularChain.d n (fundamentalChain (n + 1)))) :=
    TMap_pushforward ⟨σ.val, σ.2⟩ (SingularChain.d n (fundamentalChain (n + 1)))
  rw [h4]
  have h5 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d (n + 1) (T_fundamental (n + 1))) +
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (TMap n (SingularChain.d n (fundamentalChain (n + 1)))) =
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (SingularChain.d (n + 1) (T_fundamental (n + 1)) + TMap n (SingularChain.d n (fundamentalChain (n + 1)))) := by
    exact (SingularChain.pushforward_add ⟨σ.val, σ.2⟩
      (SingularChain.d (n + 1) (T_fundamental (n + 1)))
      (TMap n (SingularChain.d n (fundamentalChain (n + 1))))).symm
  rw [h5]
  rw [h_fund]
  have h6 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1) - fundamentalChain (n + 1)) =
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1)) -
      SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) := by
    have h_add : SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1) - fundamentalChain (n + 1)) +
        SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) =
        SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1)) := by
      have h1 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1) - fundamentalChain (n + 1)) +
          SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) =
          SingularChain.pushforward ⟨σ.val, σ.2⟩ ((sd_fundamental (n + 1) - fundamentalChain (n + 1)) + fundamentalChain (n + 1)) :=
        (SingularChain.pushforward_add ⟨σ.val, σ.2⟩
          (sd_fundamental (n + 1) - fundamentalChain (n + 1))
          (fundamentalChain (n + 1))).symm
      rw [h1]
      have h2 : (sd_fundamental (n + 1) - fundamentalChain (n + 1)) + fundamentalChain (n + 1) = sd_fundamental (n + 1) :=
        sub_add_cancel (sd_fundamental (n + 1)) (fundamentalChain (n + 1))
      rw [h2]
    exact eq_sub_of_add_eq h_add
  rw [h6]
  have h7 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1)) = sdSimplex σ := by
    simp [sdSimplex]
  have h8 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (fundamentalChain (n + 1)) = Finsupp.single σ (1 : ℤ) := by
    simp [fundamentalChain, SingularChain.pushforward, SingularChain.pushforwardSimplex, Finsupp.sum_single_index]
    ; rfl
  rw [h7, h8]

/-- Helper: in any AddCommGroup, `a + c + (b + d) = (a + b) + (c + d)`. -/
lemma add_rearrange {G : Type*} [AddCommGroup G] (a b c d : G) :
  a + c + (b + d) = (a + b) + (c + d) := by
  have h1 : a + c + (b + d) = a + (c + (b + d)) := by
    exact add_assoc a c (b + d)
  rw [h1]
  have h2 : c + (b + d) = b + (c + d) := by
    have h3 : c + (b + d) = (c + b) + d := by exact Eq.symm (add_assoc c b d)
    have h4 : c + b = b + c := add_comm c b
    rw [h3, h4] ; exact add_assoc b c d
  rw [h2] ; exact Eq.symm (add_assoc a b (c + d))

/-- Helper: in any AddCommGroup, `(a - b) + (c - d) = a + c - (b + d)`. -/
lemma sub_add_sub {G : Type*} [AddCommGroup G] (a b c d : G) :
  (a - b) + (c - d) = a + c - (b + d) := by
  have h1 : (a - b) + (c - d) = a + (-b) + (c + (-d)) := by
    have h2 : a - b = a + (-b) := by exact SubNegMonoid.sub_eq_add_neg a b
    have h3 : c - d = c + (-d) := by exact SubNegMonoid.sub_eq_add_neg c d
    rw [h2, h3]
  rw [h1]
  have h4 : a + (-b) + (c + (-d)) = a + c + (-(b + d)) := by
    have h5 : a + (-b) + (c + (-d)) = a + c + ((-b) + (-d)) := by
      exact (add_rearrange a (-b) c (-d)).symm
    rw [h5]
    have h6 : (-b) + (-d) = -(b + d) := by
      exact Eq.symm (neg_add b d)
    rw [h6]
  rw [h4]
  have h7 : a + c - (b + d) = a + c + (-(b + d)) := by exact SubNegMonoid.sub_eq_add_neg (a + c) (b + d)
  rw [h7]

/-- Helper: in any Module, `r • (x - y) = r • x - r • y`. -/
lemma smul_sub {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (r : R) (x y : M) : r • (x - y) = r • x - r • y := by
  have h1 : r • (x - y) + r • y = r • x := by
    have h2 : r • (x - y) + r • y = r • ((x - y) + y) := by
      rw [←smul_add]
    rw [h2, sub_add_cancel x y]
  exact eq_sub_of_add_eq h1

/-- Helper: from the simplex-wise homotopy property, deduce it for all chains. -/
lemma chainHomotopy_of_simplex {X : Type*} [TopologicalSpace X] (n : ℕ)
    (h_simplex : ∀ (σ : SingularSimplex X (n + 1)),
      SingularChain.d (n + 1) (TSimplex σ) + TMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
      sdSimplex σ - Finsupp.single σ (1 : ℤ)) :
    ∀ (c : SingularChain ℤ X (n + 1)),
      SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c) =
      sdMap (n + 1) c - c := by
  let P : SingularChain ℤ X (n + 1) → Prop := fun c' =>
    SingularChain.d (n + 1) (TMap (n + 1) c') + TMap n (SingularChain.d n c') =
    sdMap (n + 1) c' - c'
  have h_zero : P 0 := by
    simp [P, TMap, sdMap, SingularChain.d]
  have h_add : ∀ (σ : SingularSimplex X (n + 1)) (r : ℤ) (c' : SingularChain ℤ X (n + 1)),
      σ ∉ c'.support → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' _ _ ih
    dsimp only [P] at *
    have h1 : TMap (n + 1) (Finsupp.single σ r + c') =
        TMap (n + 1) (Finsupp.single σ r) + TMap (n + 1) c' :=
      TMap_add (n + 1) (Finsupp.single σ r) c'
    have h2 : SingularChain.d n (Finsupp.single σ r + c') =
        SingularChain.d n (Finsupp.single σ r) + SingularChain.d n c' :=
      SingularChain.d_add n (Finsupp.single σ r) c'
    have h3 : sdMap (n + 1) (Finsupp.single σ r + c') =
        sdMap (n + 1) (Finsupp.single σ r) + sdMap (n + 1) c' :=
      sdMap_add (n + 1) (Finsupp.single σ r) c'
    rw [h1, h2, h3]
    rw [SingularChain.d_add (n + 1) (TMap (n + 1) (Finsupp.single σ r)) (TMap (n + 1) c')]
    rw [TMap_add n (SingularChain.d n (Finsupp.single σ r)) (SingularChain.d n c')]
    have h_single : SingularChain.d (n + 1) (TMap (n + 1) (Finsupp.single σ r)) +
        TMap n (SingularChain.d n (Finsupp.single σ r)) =
        sdMap (n + 1) (Finsupp.single σ r) - Finsupp.single σ r := by
      have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
        simp [Finsupp.smul_single]
      rw [hsr]
      rw [TMap_smul (n + 1) r (Finsupp.single σ (1 : ℤ))]
      rw [SingularChain.d_smul (n + 1) r (TMap (n + 1) (Finsupp.single σ (1 : ℤ)))]
      rw [SingularChain.d_smul n r (Finsupp.single σ (1 : ℤ))]
      rw [TMap_smul n r (SingularChain.d n (Finsupp.single σ (1 : ℤ)))]
      rw [sdMap_smul (n + 1) r (Finsupp.single σ (1 : ℤ))]
      have h := h_simplex σ
      have h_tsimplex : TSimplex σ = TMap (n + 1) (Finsupp.single σ (1 : ℤ)) := by
        simp [TMap, Finsupp.sum_single_index]
      have h_sdsimplex : sdSimplex σ = sdMap (n + 1) (Finsupp.single σ (1 : ℤ)) := by
        have h1 : sdMap (n + 1) (Finsupp.single σ (1 : ℤ)) = sdSimplex σ := by
          dsimp only [sdMap]
          rw [Finsupp.sum_single_index]
          <;> simp
        exact h1.symm
      rw [h_tsimplex, h_sdsimplex] at h
      -- General fact: r • (x + y) = r • x + r • y and r • (x - y) = r • x - r • y
      have h_smul_main : ∀ (x y z w : SingularChain ℤ X (n + 1)),
          x + y = z - w → r • x + r • y = r • z - r • w := by
        intro x y z w hxy
        have h1 : r • (x + y) = r • x + r • y := smul_add r x y
        have h2 : r • (z - w) = r • z - r • w := smul_sub r z w
        have h5 : r • (x + y) = r • (z - w) := by rw [hxy]
        rw [h1, h2] at h5
        exact h5
      exact h_smul_main _ _ _ _ h
    have h_ih' : SingularChain.d (n + 1) (TMap (n + 1) c') + TMap n (SingularChain.d n c') =
        sdMap (n + 1) c' - c' := ih
    -- General algebraic fact: in any AddCommGroup,
    -- given a + b = s1 - x1 and c + d = s2 - x2,
    -- then a + c + (b + d) = s1 + s2 - (x1 + x2)
    let a := SingularChain.d (n + 1) (TMap (n + 1) (Finsupp.single σ r))
    let b := TMap n (SingularChain.d n (Finsupp.single σ r))
    let c := SingularChain.d (n + 1) (TMap (n + 1) c')
    let d := TMap n (SingularChain.d n c')
    let s1 := sdMap (n + 1) (Finsupp.single σ r)
    let s2 := sdMap (n + 1) c'
    let x1 := Finsupp.single σ r
    let x2 := c'
    have h1 : a + b = s1 - x1 := h_single
    have h2 : c + d = s2 - x2 := h_ih'
    have h_rearrange : a + c + (b + d) = (a + b) + (c + d) :=
      add_rearrange a b c d
    have h_sub_add : (s1 - x1) + (s2 - x2) = s1 + s2 - (x1 + x2) :=
      sub_add_sub s1 x1 s2 x2
    have h_goal : a + c + (b + d) = s1 + s2 - (x1 + x2) := by
      calc
        a + c + (b + d) = (a + b) + (c + d) := h_rearrange
        _ = (s1 - x1) + (s2 - x2) := by rw [h1, h2]
        _ = s1 + s2 - (x1 + x2) := h_sub_add
    exact h_goal
  intro c
  exact Finsupp.induction c h_zero h_add

/-- The boundary of sd_fundamental equals sdMap of the boundary of fundamentalChain.
This is the fundamental-simplex case of sd_chainMap, extracted as a separate lemma
for use in the chain homotopy proof. -/
lemma sd_fundamental_boundary (n : ℕ) :
    SingularChain.d n (sd_fundamental (n + 1)) =
    sdMap n (SingularChain.d n (fundamentalChain (n + 1))) := by
  induction n with
  | zero =>
    let X := {x // x ∈ stdSimplex ℝ (Fin 2)}
    let b : X := stdSimplex.barycenter 1
    let hs : Convex ℝ (stdSimplex ℝ (Fin 2)) := by exact convex_stdSimplex ℝ (Fin 2)
    let dι : SingularChain ℤ X 0 := SingularChain.d 0 (fundamentalChain 1)
    let sd_dι : SingularChain ℤ X 0 :=
      dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental 0)
    have h_def : sd_fundamental 1 = singularConeMap hs b.property 0 sd_dι := by
      dsimp only [sd_fundamental, Nat.casesOn] ; rfl
    have h_sd_dι_eq : sd_dι = sdMap 0 dι := by rfl
    have h_sd0_id' : sdMap 0 dι = dι := sdMap_zero_id dι
    have h_sd_dι_eq_dι : sd_dι = dι := by
      rw [h_sd_dι_eq, h_sd0_id']
    have h_main1 : SingularChain.d 0 (sd_fundamental 1) = dι := by
      rw [h_def, h_sd_dι_eq_dι]
      exact d_cone_of_boundary hs b.property (fundamentalChain 1)
    have h_main2 : sdMap 0 (SingularChain.d 0 (fundamentalChain 1)) = dι := by
      exact sdMap_zero_id dι
    rw [h_main1, h_main2]
  | succ n ih =>
    let X := {x // x ∈ stdSimplex ℝ (Fin (n + 3))}
    let b : X := stdSimplex.barycenter (n + 2)
    let hs : Convex ℝ (stdSimplex ℝ (Fin (n + 3))) := by exact convex_stdSimplex ℝ (Fin (n + 3))
    let dι : SingularChain ℤ X (n + 1) := SingularChain.d (n + 1) (fundamentalChain (n + 2))
    let sd_dι : SingularChain ℤ X (n + 1) :=
      dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental (n + 1))
    have h_def : sd_fundamental (n + 2) = singularConeMap hs b.property (n + 1) sd_dι := by
      dsimp only [sd_fundamental, Nat.casesOn] ; rfl
    have h_goal : SingularChain.d (n + 1) (sd_fundamental (n + 2)) =
        sdMap (n + 1) (SingularChain.d (n + 1) (fundamentalChain (n + 2))) := by
      rw [h_def]
      have h_cone : SingularChain.d (n + 1) (singularConeMap hs b.property (n + 1) sd_dι) =
          sd_dι - singularConeMap hs b.property n (SingularChain.d n sd_dι) :=
        singularCone.d_cone_eq hs b.property n sd_dι
      rw [h_cone]
      have h_sd_dι_def : sd_dι = sdMap (n + 1) dι := by rfl
      rw [h_sd_dι_def]
      have h_chainMap_n : ∀ (c : SingularChain ℤ X (n + 1)),
          SingularChain.d n (sdMap (n + 1) c) = sdMap n (SingularChain.d n c) :=
        sd_chainMap_of_simplex (n := n)
          (sd_simplex_chainMap_of_fundamental n ih)
      have h_d_sd : SingularChain.d n (sdMap (n + 1) dι) =
          sdMap n (SingularChain.d n dι) := h_chainMap_n dι
      rw [h_d_sd]
      have h_dd : SingularChain.d n dι = 0 := by
        dsimp only [dι]
        exact SingularChain.d_squared n (fundamentalChain (n + 2))
      rw [h_dd]
      have h_sd0 : sdMap n (0 : SingularChain ℤ X n) = 0 := by
        simp [sdMap]
      rw [h_sd0]
      have h_cone0 : singularConeMap hs b.property n (0 : SingularChain ℤ X n) = 0 := by
        simp [singularConeMap]
      rw [h_cone0]
      ; abel
    exact h_goal

/-- **Chain homotopy**: d(T(c)) + T(d(c)) = sd(c) - c.
Proved by induction on n, simultaneously for the fundamental simplex
and for all chains (using naturality). -/
theorem chainHomotopy {X : Type*} [TopologicalSpace X] (n : ℕ) :
    ∀ (c : SingularChain ℤ X (n + 1)),
      SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c) =
      sdMap (n + 1) c - c := by
  have h_fund : ∀ n : ℕ,
      SingularChain.d (n + 1) (T_fundamental (n + 1)) +
      TMap n (SingularChain.d n (fundamentalChain (n + 1))) =
      sd_fundamental (n + 1) - fundamentalChain (n + 1) := by
    intro n
    induction n with
    | zero =>
      -- Base case n = 0
      let X := {x // x ∈ stdSimplex ℝ (Fin 2)}
      let b : X := stdSimplex.barycenter 1
      let hs : Convex ℝ (stdSimplex ℝ (Fin 2)) := by exact convex_stdSimplex ℝ (Fin 2)
      let dι : SingularChain ℤ X 0 := SingularChain.d 0 (fundamentalChain 1)
      let T_dι : SingularChain ℤ X 1 :=
        dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental 0)
      let c_cone : SingularChain ℤ X 1 := sd_fundamental 1 - fundamentalChain 1 - T_dι
      have h_def : T_fundamental 1 = singularConeMap hs b.property 1 c_cone := by
        dsimp only [T_fundamental, Nat.casesOn] ; rfl
      have h_T_dι_zero : T_dι = 0 := by
        dsimp only [T_dι]
        have h_tfund0 : T_fundamental 0 = 0 := by rfl
        have h : ∀ (σ : SingularSimplex X 0) (r : ℤ),
            r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental 0) = 0 := by
          intro σ r
          rw [h_tfund0]
          have h2 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (0 : SingularChain ℤ _ 1) = 0 := by
            simp [SingularChain.pushforward]
          rw [h2]
          exact smul_zero r
        have h_sum : dι.sum (fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental 0)) = 0 := by
          have h' : ∀ (σ : SingularSimplex X 0), (dι σ) • SingularChain.pushforward ⟨σ.val, σ.2⟩ (T_fundamental 0) = 0 :=
            fun σ => h σ (dι σ)
          have h_sum' : ∑ x ∈ dι.support, (dι x) • SingularChain.pushforward ⟨x.val, x.2⟩ (T_fundamental 0) = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            exact h' x
          rw [Finsupp.sum]
          exact h_sum'
        exact h_sum
      have h_c_cone_simp : c_cone = sd_fundamental 1 - fundamentalChain 1 := by
        dsimp only [c_cone]
        rw [h_T_dι_zero] ; abel
      have h_main : SingularChain.d 1 (T_fundamental 1) = sd_fundamental 1 - fundamentalChain 1 := by
        rw [h_def, h_c_cone_simp]
        have h_cone : SingularChain.d 1 (singularConeMap hs b.property 1 (sd_fundamental 1 - fundamentalChain 1)) =
            (sd_fundamental 1 - fundamentalChain 1) -
            singularConeMap hs b.property 0 (SingularChain.d 0 (sd_fundamental 1 - fundamentalChain 1)) :=
          singularCone.d_cone_eq hs b.property 0 (sd_fundamental 1 - fundamentalChain 1)
        rw [h_cone]
        have h_d_sub : SingularChain.d 0 (sd_fundamental 1 - fundamentalChain 1) =
            SingularChain.d 0 (sd_fundamental 1) - SingularChain.d 0 (fundamentalChain 1) := by
          have h : sd_fundamental 1 - fundamentalChain 1 = sd_fundamental 1 + (-fundamentalChain 1) := by exact SubNegMonoid.sub_eq_add_neg (sd_fundamental 1) (fundamentalChain 1)
          rw [h]
          rw [SingularChain.d_add 0 (sd_fundamental 1) (-fundamentalChain 1)]
          have h_neg : SingularChain.d 0 (-fundamentalChain 1) = -SingularChain.d 0 (fundamentalChain 1) := by
            have h2 : (-1 : ℤ) • (fundamentalChain 1) = -fundamentalChain 1 := by simp
            rw [←h2]
            rw [SingularChain.d_smul 0 (-1 : ℤ) (fundamentalChain 1)] ; simp
          rw [h_neg]
          exact (sub_eq_add_neg _ _).symm
        rw [h_d_sub]
        have h_sd_chain : SingularChain.d 0 (sd_fundamental 1) = sdMap 0 (SingularChain.d 0 (fundamentalChain 1)) :=
          sd_fundamental_boundary 0
        rw [h_sd_chain]
        have h_sd0_id : sdMap 0 (SingularChain.d 0 (fundamentalChain 1)) = SingularChain.d 0 (fundamentalChain 1) :=
          sdMap_zero_id (SingularChain.d 0 (fundamentalChain 1))
        rw [h_sd0_id]
        have h_cancel : SingularChain.d 0 (fundamentalChain 1) - SingularChain.d 0 (fundamentalChain 1) = 0 := by
          exact sub_self _
        rw [h_cancel]
        have h_cone0 : singularConeMap hs b.property 0 (0 : SingularChain ℤ X 0) = 0 := by
          simp [singularConeMap]
        rw [h_cone0] ; simp
      have h_T0 : TMap 0 (SingularChain.d 0 (fundamentalChain 1)) = 0 := by
        dsimp only [TMap]
        have h_tfund0 : T_fundamental 0 = 0 := by rfl
        have h : ∀ (σ : SingularSimplex X 0) (r : ℤ),
            r • (TSimplex σ : SingularChain ℤ X 1) = 0 := by
          intro σ r
          dsimp only [TSimplex]
          rw [h_tfund0]
          have h2 : SingularChain.pushforward ⟨σ.val, σ.2⟩ (0 : SingularChain ℤ _ 1) = 0 := by
            simp [SingularChain.pushforward]
          rw [h2]
          exact smul_zero r
        have h_sum : (SingularChain.d 0 (fundamentalChain 1)).sum (fun σ r => r • (TSimplex σ)) = 0 := by
          have h' : ∀ (σ : SingularSimplex X 0), ((SingularChain.d 0 (fundamentalChain 1)) σ) • (TSimplex σ) = 0 :=
            fun σ => h σ ((SingularChain.d 0 (fundamentalChain 1)) σ)
          have h_sum' : ∑ x ∈ (SingularChain.d 0 (fundamentalChain 1)).support,
              ((SingularChain.d 0 (fundamentalChain 1)) x) • (TSimplex x) = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            exact h' x
          rw [Finsupp.sum]
          exact h_sum'
        exact h_sum
      rw [h_main, h_T0] ; simp
    | succ n ih =>
      let X := {x // x ∈ stdSimplex ℝ (Fin (n + 3))}
      let b : X := stdSimplex.barycenter (n + 2)
      let hs : Convex ℝ (stdSimplex ℝ (Fin (n + 3))) := by exact convex_stdSimplex ℝ (Fin (n + 3))
      let dι : SingularChain ℤ X (n + 1) := SingularChain.d (n + 1) (fundamentalChain (n + 2))
      let T_dι : SingularChain ℤ X (n + 2) := TMap (n + 1) dι
      let c_cone : SingularChain ℤ X (n + 2) := sd_fundamental (n + 2) - fundamentalChain (n + 2) - T_dι
      have h_def : T_fundamental (n + 2) = singularConeMap hs b.property (n + 2) c_cone := by
        dsimp only [T_fundamental, Nat.casesOn, T_dι, TMap, TSimplex] ; rfl
      have h_goal : SingularChain.d (n + 2) (T_fundamental (n + 2)) +
          TMap (n + 1) (SingularChain.d (n + 1) (fundamentalChain (n + 2))) =
          sd_fundamental (n + 2) - fundamentalChain (n + 2) := by
        rw [h_def]
        -- Apply cone boundary formula: d(cone(c)) = c - cone(d(c))
        have h_cone : SingularChain.d (n + 2) (singularConeMap hs b.property (n + 2) c_cone) =
            c_cone - singularConeMap hs b.property (n + 1) (SingularChain.d (n + 1) c_cone) :=
          singularCone.d_cone_eq hs b.property (n + 1) c_cone
        rw [h_cone]
        -- Goal: c_cone - cone(d(c_cone)) + TMap (n+1) dι = sd(ι) - ι
        -- Since c_cone = sd(ι) - ι - T_dι and T_dι = TMap (n+1) dι,
        -- this reduces to showing d(c_cone) = 0
        have h1 : c_cone + TMap (n + 1) dι = sd_fundamental (n + 2) - fundamentalChain (n + 2) := by
          dsimp only [c_cone, T_dι] ; abel
        have h_d_cone_zero : SingularChain.d (n + 1) c_cone = 0 := by
          -- Prove d(n+1)(c_cone) = 0
          -- c_cone = sd(ι) - ι - T_dι
          -- d(c_cone) = d(sd(ι)) - d(ι) - d(T_dι)
          --          = sd(d(ι)) - d(ι) - (sd(d(ι)) - d(ι))  [chain homotopy + d²=0]
          --          = 0
          have h_d_neg : ∀ (c' : SingularChain ℤ X (n + 2)),
              SingularChain.d (n + 1) (-c') = -SingularChain.d (n + 1) c' := by
            intro c'
            have h : (-1 : ℤ) • c' = -c' := by simp
            rw [←h]
            rw [SingularChain.d_smul (n + 1) (-1 : ℤ) c'] ; simp
          have h_d_sub : SingularChain.d (n + 1) c_cone =
              SingularChain.d (n + 1) (sd_fundamental (n + 2)) -
              SingularChain.d (n + 1) (fundamentalChain (n + 2)) -
              SingularChain.d (n + 1) (T_dι) := by
            dsimp only [c_cone]
            have h_sub1 : sd_fundamental (n + 2) - fundamentalChain (n + 2) - T_dι =
                sd_fundamental (n + 2) + (-fundamentalChain (n + 2)) + (-T_dι) := by
              have h : ∀ (G : Type _) [AddCommGroup G] (a b c : G),
                  a - b - c = a + (-b) + (-c) := by
                intro G _ a b c
                ; abel
              exact h (SingularChain ℤ X (n + 2)) (sd_fundamental (n + 2)) (fundamentalChain (n + 2)) T_dι
            rw [h_sub1]
            have h_d1 : SingularChain.d (n + 1) (sd_fundamental (n + 2) + (-fundamentalChain (n + 2)) + (-T_dι)) =
                SingularChain.d (n + 1) (sd_fundamental (n + 2)) +
                SingularChain.d (n + 1) (-fundamentalChain (n + 2)) +
                SingularChain.d (n + 1) (-T_dι) := by
              have h_assoc : sd_fundamental (n + 2) + (-fundamentalChain (n + 2)) + (-T_dι) =
                  sd_fundamental (n + 2) + ((-fundamentalChain (n + 2)) + (-T_dι)) := by
                exact add_assoc (sd_fundamental (n + 2)) (-fundamentalChain (n + 2)) (-T_dι)
              rw [h_assoc]
              rw [SingularChain.d_add (n + 1) (sd_fundamental (n + 2)) ((-fundamentalChain (n + 2)) + (-T_dι))]
              rw [SingularChain.d_add (n + 1) (-fundamentalChain (n + 2)) (-T_dι)]
              have h_assoc2 : SingularChain.d (n + 1) (sd_fundamental (n + 2)) +
                  (SingularChain.d (n + 1) (-fundamentalChain (n + 2)) + SingularChain.d (n + 1) (-T_dι)) =
                SingularChain.d (n + 1) (sd_fundamental (n + 2)) +
                  SingularChain.d (n + 1) (-fundamentalChain (n + 2)) +
                  SingularChain.d (n + 1) (-T_dι) := by
                exact Eq.symm (add_assoc (SingularChain.d (n + 1) (sd_fundamental (n + 2))) (SingularChain.d (n + 1) (-fundamentalChain (n + 2))) (SingularChain.d (n + 1) (-T_dι)))
              exact h_assoc2
            rw [h_d1]
            rw [h_d_neg (fundamentalChain (n + 2)), h_d_neg T_dι]
            have h_sub2 : SingularChain.d (n + 1) (sd_fundamental (n + 2)) + -SingularChain.d (n + 1) (fundamentalChain (n + 2)) + -SingularChain.d (n + 1) T_dι =
                SingularChain.d (n + 1) (sd_fundamental (n + 2)) - SingularChain.d (n + 1) (fundamentalChain (n + 2)) - SingularChain.d (n + 1) T_dι := by
              have h_generic : ∀ (G : Type _) [AddCommGroup G] (a b c : G), a + -b + -c = a - b - c := by
                intro G _ a b c
                ; abel
              exact h_generic (SingularChain ℤ X (n + 1)) _ _ _
            exact h_sub2
          rw [h_d_sub]
          -- d(sd(ι)) = sd(d(ι)) by sd_fundamental_boundary
          have h_sd_chainMap : SingularChain.d (n + 1) (sd_fundamental (n + 2)) =
              sdMap (n + 1) dι :=
            sd_fundamental_boundary (n + 1)
          rw [h_sd_chainMap]
          -- d(ι) = dι by definition
          have h_d_ι : SingularChain.d (n + 1) (fundamentalChain (n + 2)) = dι := by rfl
          rw [h_d_ι]
          -- Get chain homotopy at level n from IH
          have h_simplex_n : ∀ (σ : SingularSimplex X (n + 1)),
              SingularChain.d (n + 1) (TSimplex σ) + TMap n (SingularChain.d n (Finsupp.single σ (1 : ℤ))) =
              sdSimplex σ - Finsupp.single σ (1 : ℤ) :=
            T_simplex_homotopy_of_fundamental n ih
          have h_chain_n : ∀ (c : SingularChain ℤ X (n + 1)),
              SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c) =
              sdMap (n + 1) c - c :=
            chainHomotopy_of_simplex n h_simplex_n
          -- d n dι = 0 by d_squared
          have h_ddι : SingularChain.d n dι = 0 := by
            dsimp only [dι]
            exact SingularChain.d_squared n (fundamentalChain (n + 2))
          have h_homotopy_dι : SingularChain.d (n + 1) (TMap (n + 1) dι) + TMap n (SingularChain.d n dι) =
              sdMap (n + 1) dι - dι := h_chain_n dι
          rw [h_ddι] at h_homotopy_dι
          have h_T0 : TMap n (0 : SingularChain ℤ X n) = 0 := by
            simp [TMap]
          rw [h_T0] at h_homotopy_dι
          have h_d_T_dι : SingularChain.d (n + 1) (T_dι) = sdMap (n + 1) dι - dι := by
            dsimp only [T_dι]
            simpa using h_homotopy_dι
          rw [h_d_T_dι]
          ; abel
        rw [h_d_cone_zero]
        have h_cone0 : singularConeMap hs b.property (n + 1) (0 : SingularChain ℤ X (n + 1)) = 0 := by
          simp [singularConeMap]
        rw [h_cone0]
        ; simpa using h1
      exact h_goal
  exact chainHomotopy_of_simplex n (T_simplex_homotopy_of_fundamental n (h_fund n))

-- ============================================
-- Mesh-shrinking property of barycentric subdivision
-- ============================================

namespace stdSimplex

/-- The distance from the barycenter to any point in the standard n-simplex
    is at most n/(n+1) (in the sup norm). -/
lemma dist_barycenter_le (n : ℕ) (x : {x // x ∈ stdSimplex ℝ (Fin (n + 1))}) :
    dist x.val (barycenter n).val ≤ (n : ℝ) / (n + 1 : ℝ) := by
  have h_nonneg : 0 ≤ (n : ℝ) / (n + 1 : ℝ) := by positivity
  set b : ℝ := 1 / (n + 1 : ℝ) with hb
  have h_bary_i : ∀ i : Fin (n + 1), (barycenter n).val i = b := by
    intro i
    simp [barycenter, hb]
  have h_coords : ∀ i : Fin (n + 1), |x.val i - b| ≤ (n : ℝ) / (n + 1 : ℝ) := by
    intro i
    have hxi : 0 ≤ x.val i := x.property.1 i
    have hxi1 : x.val i ≤ 1 := by
      have h_sum : ∑ j : Fin (n + 1), x.val j = 1 := x.property.2
      have h : x.val i ≤ ∑ j : Fin (n + 1), x.val j :=
        Finset.single_le_sum (fun j _ => x.property.1 j) (Finset.mem_univ i)
      rw [h_sum] at h
      exact h
    have h_upper : x.val i - b ≤ (n : ℝ) / (n + 1 : ℝ) := by
      have h : x.val i ≤ 1 := hxi1
      have h' : (1 : ℝ) - b = (n : ℝ) / (n + 1 : ℝ) := by
        simp [hb] ; field_simp ; ring
      linarith
    have h_lower : -((n : ℝ) / (n + 1 : ℝ)) ≤ x.val i - b := by
      by_cases h_n : n = 0
      · subst h_n
        have h_i0 : i = 0 := by exact Fin.eq_zero i
        rw [h_i0]
        have h_sum : x.val 0 = 1 := by simpa using x.property.2
        linarith [hb]
      · have h_pos : 0 < n := Nat.pos_of_ne_zero h_n
        have h1 : 0 ≤ x.val i := hxi
        have h2 : -b ≤ x.val i - b := by linarith
        have h3 : -((n : ℝ) / (n + 1 : ℝ)) ≤ -b := by
          have h4 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_pos
          have h5 : (1 : ℝ) / (n + 1 : ℝ) ≤ (n : ℝ) / (n + 1 : ℝ) := by
            apply div_le_div_of_nonneg_right
            <;> linarith
          have h6 : b ≤ (n : ℝ) / (n + 1 : ℝ) := by
            simpa [hb] using h5
          linarith
        linarith
    rw [abs_le]
    constructor <;> linarith
  have h_main : ∀ i : Fin (n + 1), dist (x.val i) ((barycenter n).val i) ≤ (n : ℝ) / (n + 1 : ℝ) := by
    intro i
    have h4 : (barycenter n).val i = b := h_bary_i i
    rw [h4]
    simpa [dist_eq_norm] using h_coords i
  have h_dist_le : dist x.val (barycenter n).val ≤ (n : ℝ) / (n + 1 : ℝ) := by
    have h1 : ∀ (i : Fin (n + 1)), ‖(x.val - (barycenter n).val) i‖ ≤ (n : ℝ) / (n + 1 : ℝ) := by
      intro i
      simpa [sub_eq_add_neg, dist_eq_norm] using h_main i
    have h2 : ‖x.val - (barycenter n).val‖ ≤ (n : ℝ) / (n + 1 : ℝ) := by
      letI : ∀ (i : Fin (n + 1)), SeminormedAddCommGroup ℝ := fun _ => inferInstance
      exact (pi_norm_le_iff_of_nonneg h_nonneg).mpr h_coords
    have h3 : dist x.val (barycenter n).val = ‖x.val - (barycenter n).val‖ := by
      simp [dist_eq_norm]
    rw [h3]
    exact h2
  exact h_dist_le

end stdSimplex

-- ============================================
-- Cone diameter bound
-- ============================================

/-- The image of the cone of a singular simplex is contained in the
    convex hull of {b} ∪ range(σ). -/
lemma singularCone_image_subset_convexHull {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E} :
    Set.range (singularCone (b := b) σ) ⊆
      convexHull ℝ (insert b (Set.range σ)) := by
  intro z hz
  rcases hz with ⟨t, rfl⟩
  dsimp only [singularCone]
  let t0 : ℝ := t.val 0
  by_cases h : t0 = 1
  · rw [dif_pos h]
    exact subset_convexHull ℝ _ (Set.mem_insert b (Set.range σ))
  · rw [dif_neg h]
    have h_t0_nonneg : 0 ≤ t0 := t.prop.1 0
    have h_t0_le_one : t0 ≤ 1 := by
      have h_sum : ∑ i : Fin (k + 2), t.val i = 1 := t.prop.2
      have h : t.val 0 ≤ ∑ i : Fin (k + 2), t.val i :=
        Finset.single_le_sum (fun i _ => t.prop.1 i) (Finset.mem_univ 0)
      rw [h_sum] at h
      exact h
    have h_one_minus_nonneg : 0 ≤ 1 - t0 := by linarith
    have h_sum_coeff : t0 + (1 - t0) = 1 := by linarith
    have h1 : σ (stdSimplex.face0Proj k t h) ∈ Set.range σ :=
      ⟨stdSimplex.face0Proj k t h, rfl⟩
    have h2 : σ (stdSimplex.face0Proj k t h) ∈ convexHull ℝ (insert b (Set.range σ)) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _ h1)
    have h3 : b ∈ convexHull ℝ (insert b (Set.range σ)) :=
      subset_convexHull ℝ _ (Set.mem_insert b (Set.range σ))
    exact (convex_convexHull ℝ (insert b (Set.range σ))) h3 h2 h_t0_nonneg h_one_minus_nonneg h_sum_coeff

/-- Diameter of {b} ∪ S is at most max(diam S, sup_{s∈S} dist(b,s)). -/
lemma diam_insert_le_max {α : Type*} [PseudoMetricSpace α] {b : α} {S : Set α} {D r : ℝ}
    (hS_bdd : Bornology.IsBounded S) (hD : Metric.diam S ≤ D) (hr : ∀ x ∈ S, dist b x ≤ r) :
    Metric.diam (insert b S) ≤ max D r := by
  have hD_nonneg : 0 ≤ D := by
    have h : 0 ≤ Metric.diam S := by exact Metric.diam_nonneg
    linarith
  by_cases hS_empty : S = ∅
  · -- S is empty, so insert b S = {b}, diam = 0
    rw [hS_empty]
    have h1 : (insert b (∅ : Set α)) = ({b} : Set α) := by simp
    rw [h1]
    have h2 : Metric.diam ({b} : Set α) = 0 := by simp
    rw [h2]
    exact le_max_of_le_left hD_nonneg
  · -- S is non-empty
    have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    have hr_nonneg : 0 ≤ r := by
      rcases hS_nonempty with ⟨s, hs⟩
      have h' : 0 ≤ dist b s := dist_nonneg
      have h'' : dist b s ≤ r := hr s hs
      linarith
    have h_insert_bdd : Bornology.IsBounded (insert b S) := hS_bdd.insert b
    apply Metric.diam_le_of_forall_dist_le (le_max_of_le_right hr_nonneg)
    intro x hx y hy
    have h_x : x = b ∨ x ∈ S := by simpa [Set.mem_insert_iff] using hx
    have h_y : y = b ∨ y ∈ S := by simpa [Set.mem_insert_iff] using hy
    cases h_x with
    | inl hx_eq =>
      cases h_y with
      | inl hy_eq =>
        rw [hx_eq, hy_eq]
        simpa using le_max_of_le_right hr_nonneg
      | inr hy_in =>
        rw [hx_eq]
        have h : dist b y ≤ r := hr y hy_in
        exact le_max_of_le_right h
    | inr hx_in =>
      cases h_y with
      | inl hy_eq =>
        rw [hy_eq]
        have h : dist x b ≤ r := by
          have h' : dist x b = dist b x := dist_comm x b
          rw [h']
          exact hr x hx_in
        exact le_max_of_le_right h
      | inr hy_in =>
        have h : dist x y ≤ Metric.diam S := Metric.dist_le_diam_of_mem hS_bdd hx_in hy_in
        have h' : dist x y ≤ D := le_trans h hD
        exact le_max_of_le_left h'

/-- **Cone diameter bound**: The diameter of the cone of a singular simplex
    is at most max(diam(range σ), sup dist(b, s)). -/
theorem singularCone_diam_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {b : E} {k : ℕ}
    {σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E}
    (hσ_cont : Continuous σ)
    {D r : ℝ} (hD : Metric.diam (Set.range σ) ≤ D) (hr : ∀ x ∈ Set.range σ, dist b x ≤ r) :
    Metric.diam (Set.range (singularCone (b := b) σ)) ≤ max D r := by
  have h_univ_compact : IsCompact (Set.univ : Set {x // x ∈ stdSimplex ℝ (Fin (k + 1))}) := by exact CompactSpace.isCompact_univ
  have h_image_compact : IsCompact (σ '' (Set.univ : Set {x // x ∈ stdSimplex ℝ (Fin (k + 1))})) :=
    h_univ_compact.image hσ_cont
  have h_range_bdd : Bornology.IsBounded (Set.range σ) := by
    have h1 : Set.range σ = σ '' (Set.univ : Set {x // x ∈ stdSimplex ℝ (Fin (k + 1))}) := by simp
    rw [h1]
    exact h_image_compact.isBounded
  have h1 : Set.range (singularCone (b := b) σ) ⊆ convexHull ℝ (insert b (Set.range σ)) :=
    singularCone_image_subset_convexHull
  have h_ch_bdd : Bornology.IsBounded (convexHull ℝ (insert b (Set.range σ))) := by
    rw [isBounded_convexHull]
    exact h_range_bdd.insert b
  have h2 : Metric.diam (Set.range (singularCone (b := b) σ)) ≤
      Metric.diam (convexHull ℝ (insert b (Set.range σ))) :=
    Metric.diam_mono h1 h_ch_bdd
  have h3 : Metric.diam (convexHull ℝ (insert b (Set.range σ))) = Metric.diam (insert b (Set.range σ)) :=
    convexHull_diam (insert b (Set.range σ))
  have h4 : Metric.diam (insert b (Set.range σ)) ≤ max D r :=
    diam_insert_le_max h_range_bdd hD hr
  calc
    Metric.diam (Set.range (singularCone (b := b) σ))
      ≤ Metric.diam (convexHull ℝ (insert b (Set.range σ))) := h2
    _ = Metric.diam (insert b (Set.range σ)) := h3
    _ ≤ max D r := h4

-- ============================================
-- Mesh-shrinking for sd_fundamental
-- ============================================

/-- Helper: the image (in Euclidean space) of a singular simplex in the standard simplex. -/
def simplexImage {n : ℕ} (σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n) :
    Set (Fin (n + 1) → ℝ) :=
  Set.range (fun t : {x // x ∈ stdSimplex ℝ (Fin (n + 1))} => (σ.val t).val)

/-- Face maps don't increase diameters: the image of a set under a face map
    has diameter at most the original diameter. -/
lemma faceMap_diam_nonincrease {k : ℕ} (i : Fin (k + 2))
    (S : Set {x // x ∈ stdSimplex ℝ (Fin (k + 1))}) :
    Metric.diam (Set.image (fun x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} =>
      (stdSimplex.faceMap i x).val) S) ≤
    Metric.diam (Set.image (fun x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} => x.val) S) := by
  let f : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → Fin (k + 1) → ℝ := fun x => x.val
  let g : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → Fin (k + 2) → ℝ := fun x => (stdSimplex.faceMap i x).val
  let S' := f '' S
  have hS'_bdd : Bornology.IsBounded S' := by
    have h1 : S' ⊆ stdSimplex ℝ (Fin (k + 1)) := by
      intro z hz
      rcases hz with ⟨x, _, rfl⟩
      exact x.property
    have h2 : Bornology.IsBounded (stdSimplex ℝ (Fin (k + 1))) := by exact bounded_stdSimplex (Fin (k + 1))
    exact Bornology.IsBounded.subset h2 h1
  let gS := g '' S
  have hgS_bdd : Bornology.IsBounded gS := by
    have h1 : gS ⊆ stdSimplex ℝ (Fin (k + 2)) := by
      intro z hz
      rcases hz with ⟨x, _, rfl⟩
      exact (stdSimplex.faceMap i x).property
    have h2 : Bornology.IsBounded (stdSimplex ℝ (Fin (k + 2))) := by exact bounded_stdSimplex (Fin (k + 2))
    exact Bornology.IsBounded.subset h2 h1
  -- Helper: value of faceMap at i is 0
  have h_val_at_i : ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}), (g x) i = 0 := by
    intro x
    have h_map_val : ∀ (y : Fin (k + 2)), (g x) y =
        (Finset.univ.filter (fun (j : Fin (k + 1)) => i.succAbove j = y)).sum (fun j => x.val j) := by
      intro y
      have h1 : (g x) y = FunOnFinite.linearMap ℝ ℝ (i.succAbove) x.val y := by
        simp [g, stdSimplex.faceMap]
        ; rfl
      rw [h1]
      rw [FunOnFinite.linearMap_apply_apply]
    rw [h_map_val i]
    have h_empty : (Finset.univ.filter (fun (j : Fin (k + 1)) => i.succAbove j = i)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _
      exact Ne.symm (Fin.ne_succAbove i j)
    rw [h_empty]
    ; simp
  -- Helper: value of faceMap at i.succAbove j is x.val j
  have h_val_at_succAbove : ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}) (j : Fin (k + 1)),
      (g x) (i.succAbove j) = x.val j := by
    intro x j
    have h_map_val : ∀ (y : Fin (k + 2)), (g x) y =
        (Finset.univ.filter (fun (j' : Fin (k + 1)) => i.succAbove j' = y)).sum (fun j' => x.val j') := by
      intro y
      have h1 : (g x) y = FunOnFinite.linearMap ℝ ℝ (i.succAbove) x.val y := by
        simp [g, stdSimplex.faceMap]
        ; rfl
      rw [h1]
      rw [FunOnFinite.linearMap_apply_apply]
    rw [h_map_val (i.succAbove j)]
    have h_filter : (Finset.univ.filter (fun (j' : Fin (k + 1)) => i.succAbove j' = i.succAbove j)) = {j} := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [Fin.succAbove_inj]
    rw [h_filter]
    ; simp
  -- Main inequality: dist(g u, g v) ≤ dist(f u, f v)
  have h_main : ∀ (u v : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}),
      dist (g u) (g v) ≤ dist (f u) (f v) := by
    intro u v
    simp only [g, f, dist_eq_norm]
    letI : ∀ (j : Fin (k + 2)), SeminormedAddCommGroup ℝ := fun _ => inferInstance
    letI : ∀ (j : Fin (k + 1)), SeminormedAddCommGroup ℝ := fun _ => inferInstance
    have h1 : ∀ (j : Fin (k + 2)), ‖(g u - g v) j‖ ≤ ‖f u - f v‖ := by
      intro j
      by_cases hji : j = i
      · -- Case j = i
        rw [hji]
        have h2 : (g u - g v) i = 0 := by
          have h21 : (g u) i = 0 := h_val_at_i u
          have h22 : (g v) i = 0 := h_val_at_i v
          simp [h21, h22]
        rw [h2]
        ; simp
      · -- Case j ≠ i
        have h_exists : ∃ (j' : Fin (k + 1)), i.succAbove j' = j := by exact Fin.exists_succAbove_eq hji
        rcases h_exists with ⟨j', hj'⟩
        have h3 : (g u) j = (f u) j' := by
          have h31 : j = i.succAbove j' := Eq.symm hj'
          rw [h31]
          exact h_val_at_succAbove u j'
        have h4 : (g v) j = (f v) j' := by
          have h41 : j = i.succAbove j' := Eq.symm hj'
          rw [h41]
          exact h_val_at_succAbove v j'
        have h5 : ‖(g u - g v) j‖ = ‖(f u - f v) j'‖ := by
          have h51 : (g u - g v) j = (f u - f v) j' := by
            have h : (g u - g v) j = (g u) j - (g v) j := by
              exact Pi.sub_apply (g u) (g v) j
            rw [h, h3, h4]
            ; exact Real.ext_cauchy rfl
          rw [h51]
        rw [h5]
        have h6 : ‖(f u - f v) j'‖ ≤ ‖f u - f v‖ := by exact norm_le_pi_norm (f u - f v) j'
        exact h6
    have h7 : ‖g u - g v‖ ≤ ‖f u - f v‖ := by exact (pi_norm_le_iff_of_nonempty (g u - g v)).mpr h1
    exact h7
  apply Metric.diam_le_of_forall_dist_le (by
    have h : 0 ≤ Metric.diam S' := by exact Metric.diam_nonneg
    exact h)
  intro x hx y hy
  rcases hx with ⟨u, huS, rfl⟩
  rcases hy with ⟨v, hvS, rfl⟩
  have h6 : dist (f u) (f v) ≤ Metric.diam S' :=
    Metric.dist_le_diam_of_mem hS'_bdd (Set.mem_image_of_mem f huS) (Set.mem_image_of_mem f hvS)
  exact le_trans (h_main u v) h6

/-- **Mesh-shrinking theorem for sd_fundamental**:
    Every singular simplex in the barycentric subdivision of the fundamental
    n-simplex has image (in ℝ^{n+1} with sup norm) of diameter at most n/(n+1). -/
theorem sd_fundamental_mesh_shrinking (n : ℕ) :
    ∀ (τ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ ∈ Finsupp.support (sd_fundamental n) →
      Metric.diam (simplexImage τ) ≤ (n : ℝ) / (n + 1 : ℝ) := by
  classical
  induction n with
  | zero =>
    -- Base case n = 0
    intro τ hτ
    have h_sd0 : sd_fundamental 0 = fundamentalChain 0 := by
      dsimp only [sd_fundamental]
      ; rfl
    rw [h_sd0] at hτ
    have h_support : Finsupp.support (fundamentalChain 0) = {fundamentalSimplex 0} := by
      dsimp only [fundamentalChain]
      ; simp
    rw [h_support] at hτ
    have hτ_eq : τ = fundamentalSimplex 0 := by simpa using hτ
    rw [hτ_eq]
    dsimp only [simplexImage, fundamentalSimplex]
    have h_range : Set.range (fun t : {x // x ∈ stdSimplex ℝ (Fin 1)} =>
        ((⟨fun x => x, continuous_id⟩ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin 1)} 0).val t).val) =
        stdSimplex ℝ (Fin 1) := by
      ext z
      simp only [Set.mem_range]
      constructor
      · rintro ⟨t, rfl⟩
        exact t.property
      · intro hz
        refine' ⟨⟨z, hz⟩, _⟩
        rfl
    rw [h_range]
    have h_subsingleton : Set.Subsingleton (stdSimplex ℝ (Fin 1)) := by
      intro x hx y hy
      have hx1 : ∑ i : Fin 1, x i = 1 := hx.2
      have hy1 : ∑ i : Fin 1, y i = 1 := hy.2
      have hx0 : x 0 = 1 := by simpa [Fin.sum_univ_one] using hx1
      have hy0 : y 0 = 1 := by simpa [Fin.sum_univ_one] using hy1
      have h : ∀ (i : Fin 1), x i = y i := by
        intro i
        have hi : i = 0 := Fin.eq_zero i
        rw [hi, hx0, hy0]
      funext i
      exact h i
    have h3 : Metric.diam (stdSimplex ℝ (Fin 1)) = 0 :=
      Metric.diam_subsingleton h_subsingleton
    rw [h3]
    ; norm_num
  | succ k ih =>
    -- Inductive step
    let X := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
    let b : X := stdSimplex.barycenter (k + 1)
    let hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))) := by exact convex_stdSimplex ℝ (Fin (k + 2))
    let dι : SingularChain ℤ X k := SingularChain.d k (fundamentalChain (k + 1))
    let sd_dι : SingularChain ℤ X k :=
      dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental k)
    have h_sd_def : sd_fundamental (k + 1) = singularConeMap hs b.property k sd_dι := by rfl
    intro τ hτ
    rw [h_sd_def] at hτ
    -- Step 1: τ is a cone of some σ in sd_dι
    have h_cone_supp : Finsupp.support (singularConeMap hs b.property k sd_dι) ⊆
        (Finsupp.support sd_dι).biUnion fun σ =>
          Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      Finsupp.support_sum
    have hτ_in : τ ∈ (Finsupp.support sd_dι).biUnion fun σ =>
        Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      h_cone_supp hτ
    have h_exists1 : ∃ (σ : SingularSimplex X k),
        σ ∈ Finsupp.support sd_dι ∧ τ = singularConeSimplex hs b.property σ := by
      simp only [Finset.mem_biUnion] at hτ_in
      rcases hτ_in with ⟨σ, hσ_supp, hτ_supp⟩
      have h4 : τ ∈ Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hτ_supp
      have h6 : τ = singularConeSimplex hs b.property σ := by
        simpa [Finsupp.support_single] using h4
      exact ⟨σ, hσ_supp, h6⟩
    rcases h_exists1 with ⟨σ, hσ_supp, rfl⟩
    -- Step 2: σ comes from pushforward of sd_fundamental k along some face
    have h_sd_dι_supp : Finsupp.support sd_dι ⊆
        (Finsupp.support dι).biUnion fun σ_face =>
          Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      Finsupp.support_sum
    have hσ_in : σ ∈ (Finsupp.support dι).biUnion fun σ_face =>
        Finsupp.support ((dι σ_face) • SingularChain.pushforward
          ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      h_sd_dι_supp hσ_supp
    have h_exists2 : ∃ (σ_face : SingularSimplex X k),
        σ_face ∈ Finsupp.support dι ∧
        σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
      simp only [Finset.mem_biUnion] at hσ_in
      rcases hσ_in with ⟨σ_face, hσ_face_supp, hσ_in'⟩
      have h4 : σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
        have h5 : Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) ⊆
            Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
          Finsupp.support_smul
        exact h5 hσ_in'
      exact ⟨σ_face, hσ_face_supp, h4⟩
    rcases h_exists2 with ⟨σ_face, hσ_face_supp, hσ_push⟩
    -- Step 3: σ_face is one of the face maps
    have h_dι_eq : dι = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ) := by
      dsimp only [dι, SingularChain.d, fundamentalChain]
      rw [Finsupp.sum_single_index]
      <;> simp
    have h_dι_supp : Finsupp.support dι ⊆
        Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) Finset.univ := by
      rw [h_dι_eq]
      have h : Finsupp.support (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
        Finsupp.support_finsetSum
      have h2 : ∀ (i : Fin (k + 2)),
          Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          {SingularChain.face i (fundamentalSimplex (k + 1))} := by
        intro i
        have h3 : Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
          Finsupp.support_smul
        have h4 : Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) =
            {SingularChain.face i (fundamentalSimplex (k + 1))} := by
          simp
        rw [h4] at h3
        exact h3
      have h3 : Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) (fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ))) ⊆
          Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := by
        intro x hx
        simp only [Finset.mem_biUnion] at hx
        rcases hx with ⟨i, _, hx_in⟩
        have h4 : x ∈ ({SingularChain.face i (fundamentalSimplex (k + 1))} : Finset (SingularSimplex X k)) := h2 i hx_in
        have h5 : x = SingularChain.face i (fundamentalSimplex (k + 1)) := by simpa using h4
        rw [h5]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      exact Set.Subset.trans h h3
    have hσ_face_in : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
        SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) :=
      h_dι_supp hσ_face_supp
    have h_exists3 : ∃ (i : Fin (k + 2)),
        σ_face = SingularChain.face i (fundamentalSimplex (k + 1)) := by
      have h : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
          SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := hσ_face_in
      have h' : ∃ (i : Fin (k + 2)), i ∈ (Finset.univ : Finset (Fin (k + 2))) ∧
          SingularChain.face i (fundamentalSimplex (k + 1)) = σ_face := by
        rw [Finset.mem_image] at h
        exact h
      rcases h' with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    rcases h_exists3 with ⟨i, rfl⟩
    -- Step 4: σ is pushforwardSimplex of some τ' in sd_fundamental k
    have h_push_supp : Finsupp.support (SingularChain.pushforward
        ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
         (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ (sd_fundamental k)) ⊆
        (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
          Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      Finsupp.support_sum
    have hσ_in2 : σ ∈ (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
        Finsupp.support ((sd_fundamental k τ') • Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      h_push_supp hσ_push
    have h_exists4 : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (k + 1))} k),
        τ' ∈ Finsupp.support (sd_fundamental k) ∧
        σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
      simp only [Finset.mem_biUnion] at hσ_in2
      rcases hσ_in2 with ⟨τ', hτ'_supp, hσ_in3⟩
      have h4 : σ ∈ Finsupp.support (Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single
              (SingularChain.pushforwardSimplex
                ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
                 (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hσ_in3
      have h6 : σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
        simpa [Finsupp.support_single] using h4
      exact ⟨τ', hτ'_supp, h6⟩
    rcases h_exists4 with ⟨τ', hτ'_supp, rfl⟩
    -- By IH, τ' has diameter ≤ k/(k+1)
    have h_ih : Metric.diam (simplexImage τ') ≤ (k : ℝ) / (k + 1 : ℝ) := ih τ' hτ'_supp
    -- The pushforward along face i has diameter ≤ k/(k+1) too
    let σ_E : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → Fin (k + 2) → ℝ :=
      fun t => ((SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
        (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ').val t).val
    have hσ_E_eq : ∀ t, σ_E t = (stdSimplex.faceMap i (τ'.val t)).val := by
      intro t
      rfl
    have h_σ_diam : Metric.diam (Set.range σ_E) ≤ (k : ℝ) / (k + 1 : ℝ) := by
      have h1 : Set.range σ_E = Set.image (fun x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} =>
          (stdSimplex.faceMap i x).val) (Set.range τ'.val) := by
        ext z
        simp only [σ_E, Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨τ'.val t, Set.mem_range_self t, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          rcases hx with ⟨t, rfl⟩
          exact ⟨t, rfl⟩
      rw [h1]
      let S_img := Set.image (fun x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} => x.val) (Set.range τ'.val)
      let g_img := Set.image (fun x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} => (stdSimplex.faceMap i x).val) (Set.range τ'.val)
      have h2 : Metric.diam g_img ≤ Metric.diam S_img :=
        faceMap_diam_nonincrease i (Set.range τ'.val)
      have h3 : S_img = simplexImage τ' := by
        ext z
        simp only [S_img, simplexImage, Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
          exact ⟨y, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨τ'.val y, ⟨y, rfl⟩, rfl⟩
      rw [h3] at h2
      exact le_trans h2 h_ih
    -- Distance from barycenter to any point in the image is ≤ (k+1)/(k+2)
    have h_dist_bary : ∀ x ∈ Set.range σ_E, dist b.val x ≤ ((k + 1 : ℝ) / (k + 2 : ℝ)) := by
      intro x hx
      rcases hx with ⟨t, rfl⟩
      have h_in : σ_E t ∈ stdSimplex ℝ (Fin (k + 2)) := by
        exact ((SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
          (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ').val t).property
      have h_dist : dist (σ_E t) (stdSimplex.barycenter (k + 1)).val ≤ ((k + 1 : ℝ) / (k + 2 : ℝ)) := by
        have h_orig := stdSimplex.dist_barycenter_le (k + 1) ⟨σ_E t, h_in⟩
        have h_rhs : (↑(k + 1) : ℝ) / (↑(k + 1) + 1) = ((k + 1 : ℝ) / (k + 2 : ℝ)) := by
          norm_cast
        rw [h_rhs] at h_orig
        exact h_orig
      have h_comm : dist b.val (σ_E t) = dist (σ_E t) (stdSimplex.barycenter (k + 1)).val := by
        exact dist_comm b.val (σ_E t)
      rw [h_comm]
      exact h_dist
    -- Apply cone diameter lemma
    have hσ_E_in : ∀ (t : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}), σ_E t ∈ stdSimplex ℝ (Fin (k + 2)) :=
      fun t => ((SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
        (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ').val t).property
    let σ_cont : Continuous (fun t : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} => σ_E t) := by
      exact continuous_subtype_val.comp (SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
        (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ').2
    have h_cone_diam : Metric.diam (Set.range (singularCone (b := b.val) (fun t => σ_E t))) ≤
        max ((k : ℝ) / (k + 1 : ℝ)) (((k + 1 : ℝ) / (k + 2 : ℝ))) :=
      singularCone_diam_le σ_cont h_σ_diam h_dist_bary
    -- The image of singularConeSimplex is the same as the image of singularCone
    have h_final : simplexImage (singularConeSimplex hs b.property
        (SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
          (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ')) =
        Set.range (singularCone (b := b.val) (fun t => σ_E t)) := by
      ext z
      simp [simplexImage, singularConeSimplex, σ_E]
    rw [h_final]
    have h_max : max ((k : ℝ) / (k + 1 : ℝ)) (((k + 1 : ℝ) / (k + 2 : ℝ))) =
        ((k + 1 : ℝ) / (k + 2 : ℝ)) := by
      have h_pos1 : 0 < (k : ℝ) + 1 := by positivity
      have h_pos2 : 0 < (k : ℝ) + 2 := by positivity
      have h : (k : ℝ) / (k + 1 : ℝ) ≤ (k + 1 : ℝ) / (k + 2 : ℝ) := by
        have h' : (k : ℝ) * (k + 2 : ℝ) ≤ (k + 1 : ℝ) * (k + 1 : ℝ) := by
          nlinarith
        have h_pos1' : 0 < (k : ℝ) + 1 := by positivity
        have h_pos2' : 0 < (k : ℝ) + 2 := by positivity
        calc
          (k : ℝ) / (k + 1 : ℝ)
            = ((k : ℝ) * (k + 2 : ℝ)) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
              field_simp [h_pos1', h_pos2']
          _ ≤ ((k + 1 : ℝ) * (k + 1 : ℝ)) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
              gcongr
          _ = (k + 1 : ℝ) / (k + 2 : ℝ) := by
              field_simp [h_pos1', h_pos2']
      exact max_eq_right h
    have h_final2 : max ((k : ℝ) / (k + 1 : ℝ)) (((k + 1 : ℝ) / (k + 2 : ℝ))) ≤ (↑(k + 1) : ℝ) / (↑(k + 1) + 1) := by
      rw [h_max]
      ; norm_cast
    exact le_trans h_cone_diam h_final2

section IteratedMeshShrinking

/-- Generalized barycenter distance bound: for any linear map from the standard
    simplex to a normed space, the distance from the image of the barycenter to
    any point in the image is at most n/(n+1) times the diameter of the image. -/
lemma linear_dist_barycenter_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (A : (Fin (n + 1) → ℝ) →ₗ[ℝ] E) :
    ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (n + 1))}),
      dist (A (stdSimplex.barycenter n).val) (A x.val) ≤
      (n : ℝ) / (n + 1 : ℝ) * Metric.diam (A '' (stdSimplex ℝ (Fin (n + 1)))) := by
  let S := A '' (stdSimplex ℝ (Fin (n + 1)))
  let D := Metric.diam S
  let b_std := (stdSimplex.barycenter n).val
  let b_img := A b_std
  let r := (n : ℝ) / (n + 1 : ℝ) * D
  let e (i : Fin (n + 1)) : Fin (n + 1) → ℝ := fun j => if i = j then 1 else 0
  have hS_bounded : Bornology.IsBounded S := by
    have h1 : IsCompact (stdSimplex ℝ (Fin (n + 1))) := by exact isCompact_stdSimplex ℝ (Fin (n + 1))
    exact h1.image (by exact LinearMap.continuous_on_pi A) |>.isBounded
  have hS_conv : Convex ℝ S := (convex_stdSimplex ℝ (Fin (n + 1))).linear_image A
  have h_ball_conv : Convex ℝ (Metric.closedBall b_img r) := by exact convex_closedBall b_img r
  have h_inter_conv : Convex ℝ (S ∩ Metric.closedBall b_img r) := hS_conv.inter h_ball_conv
  have hS_eq : S = convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) := by
    have h1 : stdSimplex ℝ (Fin (n + 1)) = convexHull ℝ (Set.range (e)) := by exact Eq.symm (convexHull_basis_eq_stdSimplex ℝ (Fin (n + 1)))
    have h2 : S = A '' (stdSimplex ℝ (Fin (n + 1))) := by rfl
    rw [h2]
    have h3 : A '' (stdSimplex ℝ (Fin (n + 1))) = A '' (convexHull ℝ (Set.range (e))) := by
      rw [h1]
    rw [h3]
    have h4 : A '' (convexHull ℝ (Set.range (e))) = convexHull ℝ (A '' (Set.range (e))) :=
      A.image_convexHull (Set.range (e))
    rw [h4]
    have h5 : A '' (Set.range (e)) = Set.range (fun i : Fin (n + 1) => A (e i)) := by
      ext y
      simp [Set.mem_image, Set.mem_range]
    rw [h5]
  have h_vertices_in : ∀ (i : Fin (n + 1)), A (e i) ∈ S ∩ Metric.closedBall b_img r := by
    intro i
    have h1 : A (e i) ∈ S := by
      rw [hS_eq]
      exact subset_convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) (Set.mem_range_self i)
    have h2 : dist b_img (A (e i)) ≤ r := by
      simp only [b_img, r, dist_eq_norm]
      have h_sum : A b_std - A (e i) = ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (A (e j) - A (e i)) := by
        have h3 : b_std - e i = ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (e j - e i) := by
          set c : ℝ := 1 / (n + 1 : ℝ) with hc
          set s : Finset (Fin (n + 1)) := Finset.univ.erase i with hs
          have h_card : (s.card : ℝ) = (n : ℝ) := by
            simp [hs, Finset.card_erase_of_mem]
          have h_b_std : b_std = c • e i + ∑ j ∈ s, c • e j := by
            ext k
            simp [b_std, e, stdSimplex.barycenter, hs, c, Pi.add_apply, Pi.smul_apply]

          have h_sum_sub : ∑ j ∈ s, c • (e j - e i) = (∑ j ∈ s, c • e j) - (s.card : ℝ) • (c • e i) := by
            have h1 : ∑ j ∈ s, c • (e j - e i) = ∑ j ∈ s, (c • e j - c • e i) := by
              apply Finset.sum_congr rfl
              intro j _
              exact smul_sub c (e j) (e i)
            rw [h1]
            have h2 : ∑ j ∈ s, (c • e j - c • e i) = (∑ j ∈ s, c • e j) - ∑ j ∈ s, c • e i := by
              exact Finset.sum_sub_distrib (fun x => c • e x) fun x => c • e i
            rw [h2]
            have h3 : ∑ j ∈ s, c • e i = (s.card : ℝ) • (c • e i) := by
              have h4 : ∑ j ∈ s, c • e i = (∑ j ∈ s, c) • e i := by
                rw [Finset.sum_smul]
              rw [h4]
              have h5 : ∑ j ∈ s, c = (s.card : ℝ) * c := by
                rw [Finset.sum_const]
                ; ring
              rw [h5]
              ; rw [mul_smul]
            rw [h3]
          calc
            b_std - e i
              = (c • e i + ∑ j ∈ s, c • e j) - e i := by rw [h_b_std]
            _ = (∑ j ∈ s, c • e j) + (c • e i - e i) := by abel
            _ = (∑ j ∈ s, c • e j) - ((1 - c) • e i) := by
              have h6 : c • e i - e i = c • e i - (1 : ℝ) • e i := by simp
              have h7 : c • e i - (1 : ℝ) • e i = (c - 1 : ℝ) • e i := by
                rw [← sub_smul]
              have h8 : (c - 1 : ℝ) • e i = -((1 - c) • e i) := by
                have h9 : (c - 1 : ℝ) = -(1 - c) := by ring
                rw [h9, neg_smul]
              have h10 : c • e i - e i = -((1 - c) • e i) := by
                rw [h6, h7, h8]
              rw [h10] ; abel
            _ = (∑ j ∈ s, c • e j) - (s.card : ℝ) • (c • e i) := by
              have h6 : (1 - c) • e i = (s.card : ℝ) • (c • e i) := by
                have h7 : (1 - c) = (s.card : ℝ) * c := by
                  rw [h_card, hc] ; field_simp ; ring
                rw [h7, mul_smul]
              rw [h6]
            _ = ∑ j ∈ s, c • (e j - e i) := h_sum_sub.symm
        have h4 : A (b_std - e i) = ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (A (e j) - A (e i)) := by
          rw [h3, map_sum]
          ; apply Finset.sum_congr rfl
          ; intro j _
          ; simp [map_smul, map_sub]
        simpa [map_sub] using h4
      rw [h_sum]
      have h_norm_sum : ‖∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ ≤
          ∑ j ∈ (Finset.univ.erase i), ‖(1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ :=
        norm_sum_le _ _
      have h_smul : ∀ j ∈ (Finset.univ.erase i), ‖(1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ =
          (1 / (n + 1 : ℝ)) * ‖A (e j) - A (e i)‖ := by
        intro j _
        have h_pos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
        have h : ‖(1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ = ‖(1 / (n + 1 : ℝ))‖ * ‖A (e j) - A (e i)‖ :=
          norm_smul (1 / (n + 1 : ℝ)) (A (e j) - A (e i))
        rw [h]
        have h2 : ‖(1 / (n + 1 : ℝ))‖ = (1 / (n + 1 : ℝ)) := by
          rw [Real.norm_eq_abs, abs_of_pos h_pos]
        rw [h2]
      have h5 : ‖∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ ≤
          ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * ‖A (e j) - A (e i)‖ := by
        calc
          ‖∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖
            ≤ ∑ j ∈ (Finset.univ.erase i), ‖(1 / (n + 1 : ℝ)) • (A (e j) - A (e i))‖ := h_norm_sum
          _ = ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * ‖A (e j) - A (e i)‖ := by
            apply Finset.sum_congr rfl
            intro j hj
            exact h_smul j hj
      have h6 : ∀ j ∈ (Finset.univ.erase i), ‖A (e j) - A (e i)‖ ≤ D := by
        intro j _
        have h7 : A (e j) ∈ S := by
          rw [hS_eq]
          exact subset_convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) (Set.mem_range_self j)
        have h8 : A (e i) ∈ S := by
          rw [hS_eq]
          exact subset_convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) (Set.mem_range_self i)
        have h9 : dist (A (e j)) (A (e i)) ≤ D := Metric.dist_le_diam_of_mem hS_bounded h7 h8
        simpa [dist_eq_norm] using h9
      have h10 : ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * ‖A (e j) - A (e i)‖ ≤
          ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * D := by
        apply Finset.sum_le_sum
        intro j hj
        gcongr
        exact h6 j hj
      have h11 : ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * D = (n : ℝ) / (n + 1 : ℝ) * D := by
        have h12 : Finset.card (Finset.univ.erase i) = n := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          ; simp
        have h13 : ∑ j ∈ (Finset.univ.erase i), (1 / (n + 1 : ℝ)) * D = (Finset.card (Finset.univ.erase i) : ℝ) * ((1 / (n + 1 : ℝ)) * D) := by
          rw [Finset.sum_const]
          ; ring
        rw [h13, h12]
        ; ring
      linarith
    have h2' : A (e i) ∈ Metric.closedBall b_img r := by
      have h_comm : dist (A (e i)) b_img = dist b_img (A (e i)) := dist_comm (A (e i)) b_img
      rw [Metric.mem_closedBall, h_comm]
      exact h2
    exact ⟨h1, h2'⟩
  have h_range_subset : Set.range (fun i : Fin (n + 1) => A (e i)) ⊆ S ∩ Metric.closedBall b_img r := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact h_vertices_in i
  have h_chull_subset : convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) ⊆ S ∩ Metric.closedBall b_img r :=
    convexHull_min h_range_subset h_inter_conv
  have h_S_subset : S ⊆ Metric.closedBall b_img r := by
    have h_goal : S = convexHull ℝ (Set.range (fun i : Fin (n + 1) => A (e i))) := hS_eq
    rw [h_goal]
    intro x hx
    exact (h_chull_subset hx).2
  intro x
  have h4 : A x.val ∈ S := by
    exact ⟨x.val, x.property, rfl⟩
  have h5 : A x.val ∈ Metric.closedBall b_img r := h_S_subset h4
  have h6 : dist (A x.val) b_img ≤ r := by
    simpa [Metric.mem_closedBall] using h5
  have h7 : dist b_img (A x.val) ≤ r := by
    rw [dist_comm]
    exact h6
  exact h7

/-- A singular simplex in the standard simplex is affine if its val function
    is the restriction of an affine map (linear + translation). -/
def IsAffineSimplex {n : ℕ} (σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n) : Prop :=
  ∃ (A : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) (b : Fin (n + 1) → ℝ),
    ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (n + 1))}), (σ.val x).val = A x.val + b

namespace IsAffineSimplex

lemma image_convex {n : ℕ} {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n}
    (h : IsAffineSimplex σ) : Convex ℝ (simplexImage σ) := by
  rcases h with ⟨A, b, h_eq⟩
  have h1 : simplexImage σ = (fun x : Fin (n + 1) → ℝ => A x + b) '' (stdSimplex ℝ (Fin (n + 1))) := by
    ext y
    simp only [simplexImage, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine' ⟨x.val, x.property, _⟩
      exact (h_eq x).symm
    · rintro ⟨x, hx, rfl⟩
      refine' ⟨⟨x, hx⟩, _⟩
      exact h_eq ⟨x, hx⟩
  rw [h1]
  exact (convex_stdSimplex ℝ (Fin (n + 1))).affine_image
    { toFun := fun x => A x + b,
      linear := A,
      map_vadd' := fun x v => by simp ; abel }

lemma dist_barycenter_le {n : ℕ} {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n}
    (h : IsAffineSimplex σ) :
    ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (n + 1))}),
      dist ((σ.val ⟨(stdSimplex.barycenter n).val, (stdSimplex.barycenter n).property⟩).val) ((σ.val x).val) ≤
      (n : ℝ) / (n + 1 : ℝ) * Metric.diam (simplexImage σ) := by
  rcases h with ⟨A, b, h_eq⟩
  have h_img : simplexImage σ = (fun x : Fin (n + 1) → ℝ => A x + b) '' (stdSimplex ℝ (Fin (n + 1))) := by
    ext y
    simp only [simplexImage, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      refine' ⟨x.val, x.property, _⟩
      exact (h_eq x).symm
    · rintro ⟨x, hx, rfl⟩
      refine' ⟨⟨x, hx⟩, _⟩
      exact h_eq ⟨x, hx⟩
  have h_img2 : (fun x : Fin (n + 1) → ℝ => A x + b) '' (stdSimplex ℝ (Fin (n + 1))) =
      (fun y : Fin (n + 1) → ℝ => y + b) '' (A '' (stdSimplex ℝ (Fin (n + 1)))) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  have h_diam : Metric.diam (simplexImage σ) = Metric.diam (A '' (stdSimplex ℝ (Fin (n + 1)))) := by
    rw [h_img, h_img2]
    let e : (Fin (n + 1) → ℝ) ≃ᵢ (Fin (n + 1) → ℝ) :=
      { toFun := fun y => y + b,
        invFun := fun y => y - b,
        left_inv := fun y => by simp,
        right_inv := fun y => by simp,
        isometry_toFun := fun x y => by simp  }
    exact e.diam_image (A '' (stdSimplex ℝ (Fin (n + 1))))
  intro x
  have h2 : ((σ.val ⟨(stdSimplex.barycenter n).val, (stdSimplex.barycenter n).property⟩).val) =
      A (stdSimplex.barycenter n).val + b :=
    h_eq ⟨(stdSimplex.barycenter n).val, (stdSimplex.barycenter n).property⟩
  have h3 : (σ.val x).val = A x.val + b := h_eq x
  have h_main : dist (A (stdSimplex.barycenter n).val) (A x.val) ≤
      (n : ℝ) / (n + 1 : ℝ) * Metric.diam (A '' (stdSimplex ℝ (Fin (n + 1)))) :=
    linear_dist_barycenter_le n A x
  rw [h2, h3]
  have h4 : dist (A (stdSimplex.barycenter n).val + b) (A x.val + b) =
      dist (A (stdSimplex.barycenter n).val) (A x.val) := by
    simp [dist_eq_norm]
  rw [h4]
  rw [h_diam]
  exact h_main

end IsAffineSimplex

/-- Linear maps commute with the cone construction. -/
lemma linearMap_comp_singularCone {E F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {b : E} {k : ℕ}
    (σ : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E)
    (A : E →ₗ[ℝ] F) :
    ∀ (t : {x // x ∈ stdSimplex ℝ (Fin (k + 2))}),
      A (singularCone (b := b) σ t) =
      singularCone (b := A b) (A ∘ σ) t := by
  intro t
  dsimp only [singularCone]
  let t0 : ℝ := t.val 0
  by_cases h : t0 = 1
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    ; simp [A.map_smul, A.map_add]

/-- **Generalized mesh-shrinking theorem**: For any linear map `A` from the standard
    n-simplex to a normed space, every simplex in the barycentric subdivision has
    image diameter at most `n/(n+1)` times the diameter of the image of the whole
    standard simplex. -/
theorem sd_fundamental_mesh_shrinking_general {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (A : (Fin (n + 1) → ℝ) →ₗ[ℝ] E) :
    ∀ (τ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ ∈ Finsupp.support (sd_fundamental n) →
      Metric.diam (A '' (simplexImage τ)) ≤ (n : ℝ) / (n + 1 : ℝ) * Metric.diam (A '' (stdSimplex ℝ (Fin (n + 1)))) := by
  classical
  induction n with
  | zero =>
    -- Base case n = 0
    intro τ hτ
    have h_sd0 : sd_fundamental 0 = fundamentalChain 0 := by
      dsimp only [sd_fundamental] ; rfl
    rw [h_sd0] at hτ
    have h_support : Finsupp.support (fundamentalChain 0) = {fundamentalSimplex 0} := by
      dsimp only [fundamentalChain]
      ; simp
    rw [h_support] at hτ
    have hτ_eq : τ = fundamentalSimplex 0 := by simpa using hτ
    rw [hτ_eq]
    have h_img : A '' (simplexImage (fundamentalSimplex 0)) = A '' (stdSimplex ℝ (Fin 1)) := by
      have h1 : simplexImage (fundamentalSimplex 0) = stdSimplex ℝ (Fin 1) := by
        dsimp only [simplexImage, fundamentalSimplex]
        ext z
        simp only [Set.mem_range]
        constructor
        · rintro ⟨t, rfl⟩
          exact t.property
        · intro hz
          exact ⟨⟨z, hz⟩, rfl⟩
      rw [h1]
    rw [h_img]
    have h_subsingleton : Set.Subsingleton (stdSimplex ℝ (Fin 1)) := by
      intro x hx y hy
      have hx1 : ∑ i : Fin 1, x i = 1 := hx.2
      have hy1 : ∑ i : Fin 1, y i = 1 := hy.2
      have hx0 : x 0 = 1 := by simpa [Fin.sum_univ_one] using hx1
      have hy0 : y 0 = 1 := by simpa [Fin.sum_univ_one] using hy1
      have h : ∀ (i : Fin 1), x i = y i := by
        intro i
        have hi : i = 0 := Fin.eq_zero i
        rw [hi, hx0, hy0]
      funext i
      exact h i
    have h2 : Set.Subsingleton (A '' (stdSimplex ℝ (Fin 1))) :=
      h_subsingleton.image _
    have h3 : Metric.diam (A '' (stdSimplex ℝ (Fin 1))) = 0 :=
      Metric.diam_subsingleton h2
    rw [h3]
    ; positivity
  | succ k ih =>
    -- Inductive step
    let X := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
    let b : X := stdSimplex.barycenter (k + 1)
    let hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))) := by exact convex_stdSimplex ℝ (Fin (k + 2))
    let dι : SingularChain ℤ X k := SingularChain.d k (fundamentalChain (k + 1))
    let sd_dι : SingularChain ℤ X k :=
      dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental k)
    let D_total := Metric.diam (A '' (stdSimplex ℝ (Fin (k + 2))))
    have h_sd_def : sd_fundamental (k + 1) = singularConeMap hs b.property k sd_dι := by rfl
    intro τ hτ
    rw [h_sd_def] at hτ
    -- Step 1: τ is a cone of some σ in sd_dι
    have h_cone_supp : Finsupp.support (singularConeMap hs b.property k sd_dι) ⊆
        (Finsupp.support sd_dι).biUnion fun σ =>
          Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      Finsupp.support_sum
    have hτ_in : τ ∈ (Finsupp.support sd_dι).biUnion fun σ =>
        Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      h_cone_supp hτ
    have h_exists1 : ∃ (σ : SingularSimplex X k),
        σ ∈ Finsupp.support sd_dι ∧ τ = singularConeSimplex hs b.property σ := by
      simp only [Finset.mem_biUnion] at hτ_in
      rcases hτ_in with ⟨σ, hσ_supp, hτ_supp⟩
      have h4 : τ ∈ Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hτ_supp
      have h6 : τ = singularConeSimplex hs b.property σ := by
        simpa [Finsupp.support_single] using h4
      exact ⟨σ, hσ_supp, h6⟩
    rcases h_exists1 with ⟨σ, hσ_supp, rfl⟩
    -- Step 2: σ comes from pushforward of sd_fundamental k along some face
    have h_sd_dι_supp : Finsupp.support sd_dι ⊆
        (Finsupp.support dι).biUnion fun σ_face =>
          Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      Finsupp.support_sum
    have hσ_in : σ ∈ (Finsupp.support dι).biUnion fun σ_face =>
        Finsupp.support ((dι σ_face) • SingularChain.pushforward
          ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      h_sd_dι_supp hσ_supp
    have h_exists2 : ∃ (σ_face : SingularSimplex X k),
        σ_face ∈ Finsupp.support dι ∧
        σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
      simp only [Finset.mem_biUnion] at hσ_in
      rcases hσ_in with ⟨σ_face, hσ_face_supp, hσ_in'⟩
      have h4 : σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
        have h5 : Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) ⊆
            Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
          Finsupp.support_smul
        exact h5 hσ_in'
      exact ⟨σ_face, hσ_face_supp, h4⟩
    rcases h_exists2 with ⟨σ_face, hσ_face_supp, hσ_push⟩
    -- Step 3: σ_face is one of the face maps
    have h_dι_eq : dι = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ) := by
      dsimp only [dι, SingularChain.d, fundamentalChain]
      rw [Finsupp.sum_single_index]
      <;> simp
    have h_dι_supp : Finsupp.support dι ⊆
        Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) Finset.univ := by
      rw [h_dι_eq]
      have h : Finsupp.support (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
        Finsupp.support_finsetSum
      have h2 : ∀ (i : Fin (k + 2)),
          Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          {SingularChain.face i (fundamentalSimplex (k + 1))} := by
        intro i
        have h3 : Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
          Finsupp.support_smul
        have h4 : Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) =
            {SingularChain.face i (fundamentalSimplex (k + 1))} := by
          simp
        rw [h4] at h3
        exact h3
      have h3 : Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) (fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ))) ⊆
          Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := by
        intro x hx
        simp only [Finset.mem_biUnion] at hx
        rcases hx with ⟨i, _, hx_in⟩
        have h4 : x ∈ ({SingularChain.face i (fundamentalSimplex (k + 1))} : Finset (SingularSimplex X k)) := h2 i hx_in
        have h5 : x = SingularChain.face i (fundamentalSimplex (k + 1)) := by simpa using h4
        rw [h5]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      exact Set.Subset.trans h h3
    have hσ_face_in : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
        SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) :=
      h_dι_supp hσ_face_supp
    have h_exists3 : ∃ (i : Fin (k + 2)),
        σ_face = SingularChain.face i (fundamentalSimplex (k + 1)) := by
      have h : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
          SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := hσ_face_in
      have h' : ∃ (i : Fin (k + 2)), i ∈ (Finset.univ : Finset (Fin (k + 2))) ∧
          SingularChain.face i (fundamentalSimplex (k + 1)) = σ_face := by
        rw [Finset.mem_image] at h
        exact h
      rcases h' with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    rcases h_exists3 with ⟨i, rfl⟩
    -- Step 4: σ is pushforwardSimplex of some τ' in sd_fundamental k
    have h_push_supp : Finsupp.support (SingularChain.pushforward
        ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
         (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ (sd_fundamental k)) ⊆
        (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
          Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      Finsupp.support_sum
    have hσ_in2 : σ ∈ (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
        Finsupp.support ((sd_fundamental k τ') • Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      h_push_supp hσ_push
    have h_exists4 : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (k + 1))} k),
        τ' ∈ Finsupp.support (sd_fundamental k) ∧
        σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
      simp only [Finset.mem_biUnion] at hσ_in2
      rcases hσ_in2 with ⟨τ', hτ'_supp, hσ_in3⟩
      have h4 : σ ∈ Finsupp.support (Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single
              (SingularChain.pushforwardSimplex
                ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
                 (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hσ_in3
      have h6 : σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
        simpa [Finsupp.support_single] using h4
      exact ⟨τ', hτ'_supp, h6⟩
    rcases h_exists4 with ⟨τ', hτ'_supp, hσ_eq⟩
    -- Define the face map as a linear map
    let face_i : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 2) → ℝ) :=
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)
    have h_faceMap_val : ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}),
        (stdSimplex.faceMap i x).val = face_i x.val := by
      intro x
      simp [stdSimplex.faceMap]
      ; rfl
    let A_i : (Fin (k + 1) → ℝ) →ₗ[ℝ] E := A.comp face_i
    let D_i := Metric.diam (A_i '' (stdSimplex ℝ (Fin (k + 1))))
    have h_Di_le : D_i ≤ D_total := by
      dsimp only [D_i, A_i, D_total]
      have h_subset : A_i '' (stdSimplex ℝ (Fin (k + 1))) ⊆ A '' (stdSimplex ℝ (Fin (k + 2))) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have h1 : (stdSimplex.faceMap i ⟨x, hx⟩).val ∈ stdSimplex ℝ (Fin (k + 2)) :=
          (stdSimplex.faceMap i ⟨x, hx⟩).property
        exact ⟨(stdSimplex.faceMap i ⟨x, hx⟩).val, h1, rfl⟩
      have h_bdd : Bornology.IsBounded (A '' (stdSimplex ℝ (Fin (k + 2)))) := by
        have h1 : IsCompact (stdSimplex ℝ (Fin (k + 2))) := by exact isCompact_stdSimplex ℝ (Fin (k + 2))
        exact (h1.image (by exact LinearMap.continuous_on_pi A)).isBounded
      exact Metric.diam_mono h_subset h_bdd
    -- By IH, τ' has diameter ≤ k/(k+1) * D_i
    have h_ih : Metric.diam (A_i '' (simplexImage τ')) ≤ (k : ℝ) / (k + 1 : ℝ) * D_i :=
      ih A_i τ' hτ'_supp
    -- The image of σ under A equals the image of τ' under A_i
    let σ_E : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → E :=
      fun t => A ((σ.val t).val)
    have hσ_E_comp : σ_E = A ∘ (fun t => (σ.val t).val) := by
      funext t
      ; rfl
    have h_σ_img : Set.range σ_E = A_i '' (simplexImage τ') := by
      have hσ_val : ∀ t, (σ.val t).val = face_i (τ'.val t).val := by
        intro t
        rw [hσ_eq]
        have h2 : ((SingularChain.pushforwardSimplex ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
            (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ').val t).val =
            (stdSimplex.faceMap i (τ'.val t)).val := by rfl
        rw [h2, h_faceMap_val (τ'.val t)]
      ext z
      simp only [σ_E, Set.mem_range, Set.mem_image, simplexImage]
      constructor
      · rintro ⟨t, rfl⟩
        refine' ⟨(τ'.val t).val, ⟨t, rfl⟩, _⟩
        have h1 : A ((σ.val t).val) = A_i (τ'.val t).val := by
          rw [hσ_val t]
          ; rfl
        exact h1.symm
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        refine' ⟨t, _⟩
        have h1 : A_i (τ'.val t).val = A ((σ.val t).val) := by
          rw [hσ_val t]
          ; rfl
        exact h1.symm
    have h_σ_diam : Metric.diam (Set.range σ_E) ≤ (k : ℝ) / (k + 1 : ℝ) * D_total := by
      rw [h_σ_img]
      have h_mul : (k : ℝ) / (k + 1 : ℝ) * D_i ≤ (k : ℝ) / (k + 1 : ℝ) * D_total := by
        gcongr
      exact le_trans h_ih h_mul
    -- σ_E maps into the image of the standard simplex under A
    have hσ_E_in : ∀ t, σ_E t ∈ A '' (stdSimplex ℝ (Fin (k + 2))) := by
      intro t
      have h1 : (σ.val t).val ∈ stdSimplex ℝ (Fin (k + 2)) := (σ.val t).property
      exact ⟨_, h1, rfl⟩
    let hs' : Convex ℝ (A '' (stdSimplex ℝ (Fin (k + 2)))) :=
      (convex_stdSimplex ℝ (Fin (k + 2))).linear_image A
    let hb' : A b.val ∈ A '' (stdSimplex ℝ (Fin (k + 2))) :=
      ⟨b.val, b.property, rfl⟩
    let σ_cont : Continuous σ_E := by
      have hA_cont : Continuous A := by exact LinearMap.continuous_on_pi A
      exact hA_cont.comp (continuous_subtype_val.comp σ.2)
    -- Distance from A(b) to any point in the image is ≤ (k+1)/(k+2) * D_total
    have h_dist_bary : ∀ x ∈ Set.range σ_E, dist (A b.val) x ≤ ((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total := by
      intro x hx
      rcases hx with ⟨t, rfl⟩
      have h_in : (σ.val t).val ∈ stdSimplex ℝ (Fin (k + 2)) := (σ.val t).property
      have h_main : dist (A (stdSimplex.barycenter (k + 1)).val) (A (σ.val t).val) ≤
          ((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total := by
        have h_orig := linear_dist_barycenter_le (k + 1) A ⟨(σ.val t).val, h_in⟩
        have h_rhs : (↑(k + 1) : ℝ) / (↑(k + 1) + 1) * D_total = ((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total := by
          norm_cast
        rw [h_rhs] at h_orig
        exact h_orig
      simpa [b] using h_main
    -- The image of the cone under A is the cone of the image
    let cone_img : {x // x ∈ stdSimplex ℝ (Fin (k + 2))} → E :=
      singularCone (b := A b.val) σ_E
    have h_comm : ∀ t, A ((singularConeSimplex hs b.property σ).val t).val = cone_img t := by
      intro t
      have h1 : ((singularConeSimplex hs b.property σ).val t).val =
          singularCone (b := b.val) (fun t => (σ.val t).val) t := by
        rfl
      rw [h1]
      have h2 : A (singularCone (b := b.val) (fun t => (σ.val t).val) t) =
          singularCone (b := A b.val) σ_E t := by
        dsimp only [singularCone]
        let t0 : ℝ := t.val 0
        by_cases h : t0 = 1
        · rw [dif_pos h, dif_pos h]
        · rw [dif_neg h, dif_neg h]
          ; simp [A.map_smul, A.map_add, σ_E]
      exact h2
    have h_cone_img_eq : A '' (simplexImage (singularConeSimplex hs b.property σ)) = Set.range cone_img := by
      ext z
      simp only [Set.mem_image, simplexImage, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, (h_comm t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨((singularConeSimplex hs b.property σ).val t).val, ⟨t, rfl⟩, h_comm t⟩
    -- Apply cone diameter lemma
    have h_cone_diam : Metric.diam (Set.range cone_img) ≤
        max ((k : ℝ) / (k + 1 : ℝ) * D_total) (((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total) :=
      singularCone_diam_le σ_cont h_σ_diam h_dist_bary
    rw [h_cone_img_eq]
    have h_max : max ((k : ℝ) / (k + 1 : ℝ) * D_total) (((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total) =
        ((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total := by
      have h_pos1 : 0 < (k : ℝ) + 1 := by positivity
      have h_pos2 : 0 < (k : ℝ) + 2 := by positivity
      have h : (k : ℝ) / (k + 1 : ℝ) ≤ (k + 1 : ℝ) / (k + 2 : ℝ) := by
        have h' : (k : ℝ) * (k + 2 : ℝ) ≤ (k + 1 : ℝ) * (k + 1 : ℝ) := by nlinarith
        have h_pos1' : 0 < (k : ℝ) + 1 := by positivity
        have h_pos2' : 0 < (k : ℝ) + 2 := by positivity
        calc
          (k : ℝ) / (k + 1 : ℝ)
            = ((k : ℝ) * (k + 2 : ℝ)) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
              field_simp [h_pos1', h_pos2']
          _ ≤ ((k + 1 : ℝ) * (k + 1 : ℝ)) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by gcongr
          _ = (k + 1 : ℝ) / (k + 2 : ℝ) := by
              field_simp [h_pos1', h_pos2']
      have h_nonneg : 0 ≤ D_total := by positivity
      have h2 : (k : ℝ) / (k + 1 : ℝ) * D_total ≤ (k + 1 : ℝ) / (k + 2 : ℝ) * D_total := by
        gcongr
      exact max_eq_right h2
    rw [h_max] at h_cone_diam
    have h_final : ((k + 1 : ℝ) / (k + 2 : ℝ)) * D_total ≤ (↑(k + 1) : ℝ) / (↑(k + 1) + 1) * D_total := by
      norm_cast
    exact le_trans h_cone_diam h_final

/-- Generalized affine simplex: an m-simplex in the standard (n+1)-simplex
    whose val function is the restriction of an affine map. -/
def IsAffineSimplexGen {m n : ℕ}
    (σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} m) : Prop :=
  ∃ (A : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) (b : Fin (n + 1) → ℝ),
    ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (m + 1))}), (σ.val x).val = A x.val + b

/-- The fundamental simplex is affine (identity map). -/
lemma fundamentalSimplex_isAffine (n : ℕ) :
    IsAffineSimplex (fundamentalSimplex n) := by
  refine' ⟨LinearMap.id, 0, _⟩
  intro x
  simp [fundamentalSimplex]

/-- Face maps of the fundamental simplex are generalized affine. -/
lemma faceMap_isAffineGen {n : ℕ} (i : Fin (n + 2)) :
    IsAffineSimplexGen (SingularChain.face i (fundamentalSimplex (n + 1))) := by
  let face_i : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) :=
    FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)
  have h_faceMap_val : ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (n + 1))}),
      (stdSimplex.faceMap i x).val = face_i x.val := by
    intro x
    simp [stdSimplex.faceMap]
    ; rfl
  refine' ⟨face_i, 0, _⟩
  intro x
  have h1 : ((SingularChain.face i (fundamentalSimplex (n + 1))).val x).val =
      (stdSimplex.faceMap i x).val := by rfl
  rw [h1, h_faceMap_val x]
  ; simp

/-- Pushforward of a generalized affine simplex along an affine map
    (between different dimensional simplices). -/
lemma pushforward_isAffineGen {m k n : ℕ}
    {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (k + 1))} m}
    (hσ : IsAffineSimplexGen σ)
    {f : {x // x ∈ stdSimplex ℝ (Fin (k + 1))} → {x // x ∈ stdSimplex ℝ (Fin (n + 1))}}
    (hf_cont : Continuous f)
    (A_f : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
    (b_f : Fin (n + 1) → ℝ)
    (hf_eq : ∀ x, (f x).val = A_f x.val + b_f) :
    IsAffineSimplexGen (SingularChain.pushforwardSimplex ⟨f, hf_cont⟩ σ) := by
  rcases hσ with ⟨A_σ, b_σ, hσ_eq⟩
  refine' ⟨A_f.comp A_σ, A_f b_σ + b_f, _⟩
  intro x
  have h1 : ((SingularChain.pushforwardSimplex ⟨f, hf_cont⟩ σ).val x).val = (f (σ.val x)).val := by rfl
  rw [h1, hf_eq (σ.val x), hσ_eq x]
  ; simp [LinearMap.comp_apply]
  ; abel

/-- Pushforward of an IsAffineSimplex along an affine map is IsAffineSimplex. -/
lemma pushforward_isAffine {n : ℕ}
    {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n}
    (hσ : IsAffineSimplex σ)
    {f : {x // x ∈ stdSimplex ℝ (Fin (n + 1))} → {x // x ∈ stdSimplex ℝ (Fin (n + 1))}}
    (hf_cont : Continuous f)
    (A_f : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
    (b_f : Fin (n + 1) → ℝ)
    (hf_eq : ∀ x, (f x).val = A_f x.val + b_f) :
    IsAffineSimplex (SingularChain.pushforwardSimplex ⟨f, hf_cont⟩ σ) :=
  pushforward_isAffineGen hσ hf_cont A_f b_f hf_eq

/-- The cone of a generalized affine k-simplex in the standard (k+2)-simplex
    is an affine (k+1)-simplex. -/
lemma cone_isAffine {k : ℕ}
    {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (k + 2))} k}
    (hσ : IsAffineSimplexGen σ)
    {b : {x // x ∈ stdSimplex ℝ (Fin (k + 2))}}
    (hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))))
    (hb : b.val ∈ stdSimplex ℝ (Fin (k + 2))) :
    IsAffineSimplex (singularConeSimplex hs hb σ) := by
  rcases hσ with ⟨A_σ, b_σ, hσ_eq⟩
  -- Define the linear part of the cone
  let succ_restrict : (Fin (k + 2) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
    { toFun := fun t i => t (Fin.succ i),
      map_add' := by intro t s; funext i; rfl,
      map_smul' := by intro c t; funext i; rfl }
  let v : (Fin (k + 2) → ℝ) := b.val - b_σ
  let L_cone : (Fin (k + 2) → ℝ) →ₗ[ℝ] (Fin (k + 2) → ℝ) :=
    { toFun := fun t => t 0 • v + A_σ (succ_restrict t),
      map_add' := by
        intro t s
        have h1 : (t + s) 0 • v = t 0 • v + s 0 • v := by
          simp [add_smul]
        have h21 : succ_restrict (t + s) = succ_restrict t + succ_restrict s := by
          exact succ_restrict.map_add t s
        have h2 : A_σ (succ_restrict (t + s)) = A_σ (succ_restrict t) + A_σ (succ_restrict s) := by
          rw [h21, map_add A_σ]
        rw [h1, h2]
        ; abel,
      map_smul' := by
        intro c t
        have h1 : (c • t) 0 • v = c • (t 0 • v) := by
          simp [smul_smul]
        have h21 : succ_restrict (c • t) = c • succ_restrict t := by
          exact succ_restrict.map_smul c t
        have h2 : A_σ (succ_restrict (c • t)) = c • A_σ (succ_restrict t) := by
          rw [h21, map_smul A_σ]
        rw [h1, h2]
        ; simp [smul_add]
         }
  refine' ⟨L_cone, b_σ, _⟩
  intro t
  have h_main : ((singularConeSimplex hs hb σ).val t).val = L_cone t.val + b_σ := by
    dsimp only [singularConeSimplex]
    let t0 : ℝ := t.val 0
    by_cases h : t0 = 1
    · -- Case t0 = 1
      have h_cone_eq : singularCone (b := b.val) (fun t => (σ.val t).val) t = b.val := by
        dsimp only [singularCone]
        rw [dif_pos h]
      have h_sum0 : ∀ i : Fin (k + 1), t.val (Fin.succ i) = 0 := by
        intro i
        have h_sum : ∑ j : Fin (k + 2), t.val j = 1 := t.property.2
        have h_t0 : t.val 0 = 1 := h
        have h_nonneg : ∀ j : Fin (k + 2), 0 ≤ t.val j := t.property.1
        have h_all : ∑ j : Fin (k + 2), t.val j = t.val 0 + ∑ j : Fin (k + 1), t.val (Fin.succ j) := by
          rw [Fin.sum_univ_succ]
        rw [h_all, h_t0] at h_sum
        have h' : ∑ j : Fin (k + 1), t.val (Fin.succ j) = 0 := by linarith
        have h_nonneg' : ∀ j : Fin (k + 1), 0 ≤ t.val (Fin.succ j) := fun j => h_nonneg (Fin.succ j)
        have h_eq : ∀ j : Fin (k + 1), t.val (Fin.succ j) = 0 := by
          have h_univ := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg' j)).mp h'
          intro j
          exact h_univ j (Finset.mem_univ j)
        exact h_eq i
      have h_Aσ_zero : A_σ (fun i : Fin (k + 1) => t.val (Fin.succ i)) = 0 := by
        have h : (fun i : Fin (k + 1) => t.val (Fin.succ i)) = 0 := by
          funext i
          exact h_sum0 i
        rw [h]
        exact A_σ.map_zero
      have h_L_cone : L_cone t.val + b_σ = b.val := by
        have h2 : A_σ (succ_restrict t.val) = 0 := by
          have h3 : succ_restrict t.val = fun i : Fin (k + 1) => t.val (Fin.succ i) := by rfl
          rw [h3]
          exact h_Aσ_zero
        have h_eq : L_cone t.val = t.val 0 • v + A_σ (succ_restrict t.val) := by rfl
        have h_t0 : t.val 0 = 1 := h
        rw [h_eq, h2, h_t0]
        ; simp [v, sub_add_cancel]
      rw [h_cone_eq, h_L_cone]
    · -- Case t0 ≠ 1
      have h1t : 1 - t0 ≠ 0 := by
        intro h2
        have : t0 = 1 := by linarith
        exact h this
      have h_cone_eq : singularCone (b := b.val) (fun t => (σ.val t).val) t =
          t0 • b.val + (1 - t0) • (σ.val (stdSimplex.face0Proj k t h)).val := by
        dsimp only [singularCone]
        rw [dif_neg h]
      rw [h_cone_eq]
      have h_σ_val : (σ.val (stdSimplex.face0Proj k t h)).val =
          A_σ (stdSimplex.face0Proj k t h).val + b_σ := hσ_eq (stdSimplex.face0Proj k t h)
      rw [h_σ_val]
      have h_face0Proj_val : (stdSimplex.face0Proj k t h).val =
          (1 / (1 - t0)) • (fun i : Fin (k + 1) => t.val (Fin.succ i)) := by
        funext i
        simp [stdSimplex.face0Proj, div_eq_mul_inv]
        ; ring
      have h_Aσ_face : A_σ (stdSimplex.face0Proj k t h).val =
          (1 / (1 - t0)) • A_σ (fun i : Fin (k + 1) => t.val (Fin.succ i)) := by
        rw [h_face0Proj_val, A_σ.map_smul]
      rw [h_Aσ_face]
      have h_final : t0 • b.val + (1 - t0) • ((1 / (1 - t0)) • A_σ (fun i : Fin (k + 1) => t.val (Fin.succ i)) + b_σ) =
          L_cone t.val + b_σ := by
        set y := A_σ (fun i : Fin (k + 1) => t.val (Fin.succ i)) with hy_def
        have h_succ : succ_restrict t.val = fun i : Fin (k + 1) => t.val (Fin.succ i) := by rfl
        have h_Lc_eq : L_cone t.val = t.val 0 • v + A_σ (succ_restrict t.val) := by rfl
        have h3 : (1 - t0) * (1 / (1 - t0)) = 1 := by
          field_simp [h1t]
        have h4 : (1 - t0) • ((1 / (1 - t0)) • y) = y := by
          calc
            (1 - t0) • ((1 / (1 - t0)) • y)
              = ((1 - t0) * (1 / (1 - t0))) • y := by rw [smul_smul]
            _ = (1 : ℝ) • y := by rw [h3]
            _ = y := by simp
        have h5 : t0 • b.val + (1 - t0) • ((1 / (1 - t0)) • y + b_σ) =
            t0 • b.val + y + (1 - t0) • b_σ := by
          rw [smul_add]
          rw [h4]
          ; abel
        have h6 : t0 • (b.val - b_σ) + y + b_σ = t0 • b.val + y + (1 - t0) • b_σ := by
          have h7 : t0 • (b.val - b_σ) = t0 • b.val - t0 • b_σ := by
            rw [smul_sub]
          have h8 : (1 - t0 : ℝ) • b_σ = b_σ - t0 • b_σ := by
            have h9 : (1 - t0 : ℝ) • b_σ = (1 : ℝ) • b_σ - t0 • b_σ := by
              rw [sub_smul]
            rw [h9] ; simp
          rw [h7, h8] ; abel
        have h10 : t0 • b.val + (1 - t0) • ((1 / (1 - t0)) • y + b_σ) =
            L_cone t.val + b_σ := by
          have h_Lc : L_cone t.val = t0 • v + y := by
            have h13 : L_cone t.val = t.val 0 • v + A_σ (succ_restrict t.val) := by rfl
            have h14 : t.val 0 = t0 := by rfl
            have h15 : succ_restrict t.val = fun i : Fin (k + 1) => t.val (Fin.succ i) := by rfl
            rw [h13, h14, h15]
          calc
            t0 • b.val + (1 - t0) • ((1 / (1 - t0)) • y + b_σ)
              = t0 • b.val + ((1 - t0) • ((1 / (1 - t0)) • y) + (1 - t0) • b_σ) := by
                rw [smul_add]
            _ = t0 • b.val + (y + (1 - t0) • b_σ) := by
                have h4 : (1 - t0) • ((1 / (1 - t0)) • y) = y := h4
                rw [h4]
            _ = t0 • b.val + y + (1 - t0) • b_σ := by
                have h_assoc : t0 • b.val + (y + (1 - t0) • b_σ) = (t0 • b.val + y) + (1 - t0) • b_σ :=
                  (add_assoc (t0 • b.val) y ((1 - t0) • b_σ)).symm
                exact h_assoc
            _ = t0 • (b.val - b_σ) + y + b_σ := by
                have h7 : t0 • (b.val - b_σ) = t0 • b.val - t0 • b_σ := by
                  exact smul_sub t0 (↑b) b_σ
                have h8 : (1 - t0 : ℝ) • b_σ = b_σ - t0 • b_σ := by
                  have h9 : (1 - t0 : ℝ) • b_σ = (1 : ℝ) • b_σ - t0 • b_σ := by
                    rw [sub_smul]
                  rw [h9]
                  ; simp
                rw [h7, h8]
                ; abel
            _ = (t0 • v + y) + b_σ := by
                have h_v : v = b.val - b_σ := by rfl
                rw [h_v]
            _ = L_cone t.val + b_σ := by
                rw [h_Lc]
        exact h10
      exact h_final
  exact h_main

/-- Every simplex in sd_fundamental n is affine. -/
theorem sd_fundamental_all_affine (n : ℕ) :
    ∀ (τ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ ∈ Finsupp.support (sd_fundamental n) → IsAffineSimplex τ := by
  classical
  induction n with
  | zero =>
    intro τ hτ
    have h_sd0 : sd_fundamental 0 = fundamentalChain 0 := by
      dsimp only [sd_fundamental] ; rfl
    rw [h_sd0] at hτ
    have h_support : Finsupp.support (fundamentalChain 0) = {fundamentalSimplex 0} := by
      dsimp only [fundamentalChain]
      ; simp
    rw [h_support] at hτ
    have hτ_eq : τ = fundamentalSimplex 0 := by simpa using hτ
    rw [hτ_eq]
    exact fundamentalSimplex_isAffine 0
  | succ k ih =>
    let X := {x // x ∈ stdSimplex ℝ (Fin (k + 2))}
    let b : X := stdSimplex.barycenter (k + 1)
    let hs : Convex ℝ (stdSimplex ℝ (Fin (k + 2))) := by exact convex_stdSimplex ℝ (Fin (k + 2))
    let dι : SingularChain ℤ X k := SingularChain.d k (fundamentalChain (k + 1))
    let sd_dι : SingularChain ℤ X k :=
      dι.sum fun σ r => r • SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental k)
    have h_sd_def : sd_fundamental (k + 1) = singularConeMap hs b.property k sd_dι := by rfl
    intro τ hτ
    rw [h_sd_def] at hτ
    -- τ is a cone of some σ in sd_dι
    have h_cone_supp : Finsupp.support (singularConeMap hs b.property k sd_dι) ⊆
        (Finsupp.support sd_dι).biUnion fun σ =>
          Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      Finsupp.support_sum
    have hτ_in : τ ∈ (Finsupp.support sd_dι).biUnion fun σ =>
        Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
      h_cone_supp hτ
    have h_exists1 : ∃ (σ : SingularSimplex X k),
        σ ∈ Finsupp.support sd_dι ∧ τ = singularConeSimplex hs b.property σ := by
      simp only [Finset.mem_biUnion] at hτ_in
      rcases hτ_in with ⟨σ, hσ_supp, hτ_supp⟩
      have h4 : τ ∈ Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_dι σ) • Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (singularConeSimplex hs b.property σ) (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hτ_supp
      have h6 : τ = singularConeSimplex hs b.property σ := by
        simpa [Finsupp.support_single] using h4
      exact ⟨σ, hσ_supp, h6⟩
    rcases h_exists1 with ⟨σ, hσ_supp, rfl⟩
    -- σ comes from pushforward of sd_fundamental k along some face
    have h_sd_dι_supp : Finsupp.support sd_dι ⊆
        (Finsupp.support dι).biUnion fun σ_face =>
          Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      Finsupp.support_sum
    have hσ_in : σ ∈ (Finsupp.support dι).biUnion fun σ_face =>
        Finsupp.support ((dι σ_face) • SingularChain.pushforward
          ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
      h_sd_dι_supp hσ_supp
    have h_exists2 : ∃ (σ_face : SingularSimplex X k),
        σ_face ∈ Finsupp.support dι ∧
        σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
      simp only [Finset.mem_biUnion] at hσ_in
      rcases hσ_in with ⟨σ_face, hσ_face_supp, hσ_in'⟩
      have h4 : σ ∈ Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) := by
        have h5 : Finsupp.support ((dι σ_face) • SingularChain.pushforward
            ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) ⊆
            Finsupp.support (SingularChain.pushforward ⟨σ_face.val, σ_face.2⟩ (sd_fundamental k)) :=
          Finsupp.support_smul
        exact h5 hσ_in'
      exact ⟨σ_face, hσ_face_supp, h4⟩
    rcases h_exists2 with ⟨σ_face, hσ_face_supp, hσ_push⟩
    -- σ_face is one of the face maps
    have h_dι_eq : dι = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ) := by
      dsimp only [dι, SingularChain.d, fundamentalChain]
      rw [Finsupp.sum_single_index]
      <;> simp
    have h_dι_supp : Finsupp.support dι ⊆
        Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) Finset.univ := by
      rw [h_dι_eq]
      have h : Finsupp.support (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
          Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
        Finsupp.support_finsetSum
      have h2 : ∀ (i : Fin (k + 2)),
          Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
          {SingularChain.face i (fundamentalSimplex (k + 1))} := by
        intro i
        have h3 : Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
            Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) :=
          Finsupp.support_smul
        have h4 : Finsupp.support (Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ)) =
            {SingularChain.face i (fundamentalSimplex (k + 1))} := by
          simp
        rw [h4] at h3
        exact h3
      have h3 : Finset.biUnion (Finset.univ : Finset (Fin (k + 2))) (fun i =>
            Finsupp.support ((-1 : ℤ) ^ (i : ℕ) •
              Finsupp.single (SingularChain.face i (fundamentalSimplex (k + 1))) (1 : ℤ))) ⊆
          Finset.image (fun i : Fin (k + 2) => SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := by
        intro x hx
        simp only [Finset.mem_biUnion] at hx
        rcases hx with ⟨i, _, hx_in⟩
        have h4 : x ∈ ({SingularChain.face i (fundamentalSimplex (k + 1))} : Finset (SingularSimplex X k)) := h2 i hx_in
        have h5 : x = SingularChain.face i (fundamentalSimplex (k + 1)) := by simpa using h4
        rw [h5]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      exact Set.Subset.trans h h3
    have hσ_face_in : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
        SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) :=
      h_dι_supp hσ_face_supp
    have h_exists3 : ∃ (i : Fin (k + 2)),
        σ_face = SingularChain.face i (fundamentalSimplex (k + 1)) := by
      have h : σ_face ∈ Finset.image (fun i : Fin (k + 2) =>
          SingularChain.face i (fundamentalSimplex (k + 1))) (Finset.univ : Finset (Fin (k + 2))) := hσ_face_in
      have h' : ∃ (i : Fin (k + 2)), i ∈ (Finset.univ : Finset (Fin (k + 2))) ∧
          SingularChain.face i (fundamentalSimplex (k + 1)) = σ_face := by
        rw [Finset.mem_image] at h
        exact h
      rcases h' with ⟨i, _, rfl⟩
      exact ⟨i, rfl⟩
    rcases h_exists3 with ⟨i, rfl⟩
    -- σ is pushforwardSimplex of some τ' in sd_fundamental k
    have h_push_supp : Finsupp.support (SingularChain.pushforward
        ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
         (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ (sd_fundamental k)) ⊆
        (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
          Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      Finsupp.support_sum
    have hσ_in2 : σ ∈ (Finsupp.support (sd_fundamental k)).biUnion fun τ' =>
        Finsupp.support ((sd_fundamental k τ') • Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
      h_push_supp hσ_push
    have h_exists4 : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (k + 1))} k),
        τ' ∈ Finsupp.support (sd_fundamental k) ∧
        σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
      simp only [Finset.mem_biUnion] at hσ_in2
      rcases hσ_in2 with ⟨τ', hτ'_supp, hσ_in3⟩
      have h4 : σ ∈ Finsupp.support (Finsupp.single
          (SingularChain.pushforwardSimplex
            ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
             (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) := by
        have h5 : Finsupp.support ((sd_fundamental k τ') • Finsupp.single
            (SingularChain.pushforwardSimplex
              ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
               (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) ⊆
            Finsupp.support (Finsupp.single
              (SingularChain.pushforwardSimplex
                ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
                 (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ') (1 : ℤ)) :=
          Finsupp.support_smul
        exact h5 hσ_in3
      have h6 : σ = SingularChain.pushforwardSimplex
          ⟨(SingularChain.face i (fundamentalSimplex (k + 1))).val,
           (SingularChain.face i (fundamentalSimplex (k + 1))).2⟩ τ' := by
        simpa [Finsupp.support_single] using h4
      exact ⟨τ', hτ'_supp, h6⟩
    rcases h_exists4 with ⟨τ', hτ'_supp, hσ_eq⟩
    -- τ' is affine by IH
    have hτ'_affine : IsAffineSimplex τ' := ih τ' hτ'_supp
    -- face i is generalized affine
    have h_face_affine : IsAffineSimplexGen (SingularChain.face i (fundamentalSimplex (k + 1))) :=
      faceMap_isAffineGen i
    -- σ is generalized affine (composition)
    let face_i : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 2) → ℝ) :=
      FunOnFinite.linearMap ℝ ℝ (Fin.succAbove i)
    have h_faceMap_val : ∀ (x : {x // x ∈ stdSimplex ℝ (Fin (k + 1))}),
        (stdSimplex.faceMap i x).val = face_i x.val := by
      intro x
      simp [stdSimplex.faceMap]
      ; rfl
    have hσ_affine : IsAffineSimplexGen σ := by
      rw [hσ_eq]
      exact pushforward_isAffineGen hτ'_affine
        (SingularChain.face i (fundamentalSimplex (k + 1))).2
        face_i 0
        (fun x => by
          have h : ((SingularChain.face i (fundamentalSimplex (k + 1))).val x).val =
              (stdSimplex.faceMap i x).val := by rfl
          rw [h]
          have h2 : (stdSimplex.faceMap i x).val = face_i x.val := h_faceMap_val x
          rw [h2]
          ; simp)
    -- cone of affine simplex is affine
    exact cone_isAffine hσ_affine hs b.property

/-- Iterated barycentric subdivision chain. -/
def sdIterate (n : ℕ) (k : ℕ) : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n :=
  Nat.recOn k (fundamentalChain n) (fun _ c => sdMap n c)

/-- Key lemma: if σ is an affine n-simplex, then every simplex in sdSimplex σ
    has diameter ≤ n/(n+1) * diam(simplexImage σ). -/
lemma sdSimplex_shrinks {n : ℕ}
    {σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n}
    (hσ : IsAffineSimplex σ) :
    ∀ (τ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ ∈ Finsupp.support (sdSimplex σ) →
      Metric.diam (simplexImage τ) ≤ (n : ℝ) / (n + 1 : ℝ) * Metric.diam (simplexImage σ) := by
  classical
  rcases hσ with ⟨A_σ, b_σ, hσ_eq⟩
  have h_img_σ : simplexImage σ = (fun x => A_σ x + b_σ) '' (stdSimplex ℝ (Fin (n + 1))) := by
    ext y
    simp only [simplexImage, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, (hσ_eq x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hσ_eq ⟨x, hx⟩⟩
  have h_diam_σ : Metric.diam (simplexImage σ) = Metric.diam (A_σ '' (stdSimplex ℝ (Fin (n + 1)))) := by
    rw [h_img_σ]
    let e : (Fin (n + 1) → ℝ) ≃ᵢ (Fin (n + 1) → ℝ) :=
      { toFun := fun y => y + b_σ,
        invFun := fun y => y - b_σ,
        left_inv := fun y => by simp,
        right_inv := fun y => by simp,
        isometry_toFun := fun x y => by simp  }
    have h_set_eq : (fun x : Fin (n + 1) → ℝ => A_σ x + b_σ) '' (stdSimplex ℝ (Fin (n + 1))) =
        e '' (A_σ '' (stdSimplex ℝ (Fin (n + 1)))) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨A_σ x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [h_set_eq]
    exact e.diam_image (A_σ '' (stdSimplex ℝ (Fin (n + 1))))
  intro τ hτ
  have h1 : τ ∈ Finsupp.support (SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n)) := by
    simpa [sdSimplex] using hτ
  have h_push_supp : Finsupp.support (SingularChain.pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n)) ⊆
      (Finsupp.support (sd_fundamental n)).biUnion fun τ' =>
        Finsupp.support ((sd_fundamental n τ') • Finsupp.single
          (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') (1 : ℤ)) :=
    Finsupp.support_sum
  have hτ_in : τ ∈ (Finsupp.support (sd_fundamental n)).biUnion fun τ' =>
      Finsupp.support ((sd_fundamental n τ') • Finsupp.single
        (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') (1 : ℤ)) :=
    h_push_supp h1
  have h_exists : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ' ∈ Finsupp.support (sd_fundamental n) ∧
      τ = SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ' := by
    simp only [Finset.mem_biUnion] at hτ_in
    rcases hτ_in with ⟨τ', hτ'_supp, hτ_in'⟩
    have h4 : τ ∈ Finsupp.support (Finsupp.single
        (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') (1 : ℤ)) := by
      have h5 : Finsupp.support ((sd_fundamental n τ') • Finsupp.single
          (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') (1 : ℤ)) ⊆
          Finsupp.support (Finsupp.single
            (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') (1 : ℤ)) :=
        Finsupp.support_smul
      exact h5 hτ_in'
    have h6 : τ = SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ' := by
      simpa [Finsupp.support_single] using h4
    exact ⟨τ', hτ'_supp, h6⟩
  rcases h_exists with ⟨τ', hτ'_supp, rfl⟩
  have h_img_τ : simplexImage (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ') =
      (fun x => A_σ x + b_σ) '' (simplexImage τ') := by
    ext z
    simp only [simplexImage, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨t, rfl⟩
      refine' ⟨(τ'.val t).val, ⟨t, rfl⟩, _⟩
      have h1 : (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ').val t = σ.val (τ'.val t) := by rfl
      have h : ((SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ').val t).val = A_σ (τ'.val t).val + b_σ := by
        rw [h1]
        exact hσ_eq (τ'.val t)
      exact h.symm
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      refine' ⟨t, _⟩
      have h1 : (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ').val t = σ.val (τ'.val t) := by rfl
      have h : ((SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ').val t).val = A_σ (τ'.val t).val + b_σ := by
        rw [h1]
        exact hσ_eq (τ'.val t)
      exact h
  have h_diam_τ : Metric.diam (simplexImage (SingularChain.pushforwardSimplex ⟨σ.val, σ.2⟩ τ')) =
      Metric.diam (A_σ '' (simplexImage τ')) := by
    rw [h_img_τ]
    let e : (Fin (n + 1) → ℝ) ≃ᵢ (Fin (n + 1) → ℝ) :=
      { toFun := fun y => y + b_σ,
        invFun := fun y => y - b_σ,
        left_inv := fun y => by simp,
        right_inv := fun y => by simp,
        isometry_toFun := fun x y => by simp  }
    have h_set_eq : (fun x : Fin (n + 1) → ℝ => A_σ x + b_σ) '' (simplexImage τ') =
        e '' (A_σ '' (simplexImage τ')) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨A_σ x, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [h_set_eq]
    exact e.diam_image (A_σ '' (simplexImage τ'))
  rw [h_diam_τ]
  have h_main : Metric.diam (A_σ '' (simplexImage τ')) ≤
      (n : ℝ) / (n + 1 : ℝ) * Metric.diam (A_σ '' (stdSimplex ℝ (Fin (n + 1)))) :=
    sd_fundamental_mesh_shrinking_general n A_σ τ' hτ'_supp
  have h_final : (n : ℝ) / (n + 1 : ℝ) * Metric.diam (A_σ '' (stdSimplex ℝ (Fin (n + 1)))) =
      (n : ℝ) / (n + 1 : ℝ) * Metric.diam (simplexImage σ) := by
    rw [h_diam_σ]
  exact le_trans h_main (le_of_eq h_final)

/-- Diameter of the standard simplex (in sup norm) is at most 1. -/
lemma stdSimplex_diam_le_one (n : ℕ) :
    Metric.diam (stdSimplex ℝ (Fin (n + 1))) ≤ 1 := by
  have h_bdd : Bornology.IsBounded (stdSimplex ℝ (Fin (n + 1))) := by
    have h1 : IsCompact (stdSimplex ℝ (Fin (n + 1))) := by exact isCompact_stdSimplex ℝ (Fin (n + 1))
    exact h1.isBounded
  apply Metric.diam_le_of_forall_dist_le (by exact zero_le_one' ℝ)
  intro x hx y hy
  have h2 : ∀ (i : Fin (n + 1)), |x i - y i| ≤ 1 := by
    intro i
    have hx_i : 0 ≤ x i := hx.1 i
    have hx_i' : x i ≤ 1 := by
      have h_sum : ∑ j : Fin (n + 1), x j = 1 := hx.2
      have h : x i ≤ ∑ j : Fin (n + 1), x j :=
        Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      rw [h_sum] at h
      exact h
    have hy_i : 0 ≤ y i := hy.1 i
    have hy_i' : y i ≤ 1 := by
      have h_sum : ∑ j : Fin (n + 1), y j = 1 := hy.2
      have h : y i ≤ ∑ j : Fin (n + 1), y j :=
        Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)
      rw [h_sum] at h
      exact h
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h3 : dist x y ≤ 1 := by
    have h4 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [h4]
    exact (pi_norm_le_iff_of_nonempty (x - y)).mpr h2
  exact h3

/-- **Iterated mesh-shrinking theorem**: Every simplex in the k-th iterated
    barycentric subdivision of the fundamental n-simplex is affine and has
    diameter at most `(n/(n+1))^k`. -/
theorem iterated_mesh_shrinking (n : ℕ) (k : ℕ) :
    ∀ (σ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      σ ∈ Finsupp.support (sdIterate n k) →
      IsAffineSimplex σ ∧ Metric.diam (simplexImage σ) ≤ ((n : ℝ) / (n + 1 : ℝ)) ^ k := by
  classical
  induction k with
  | zero =>
    intro σ hσ
    have h1 : sdIterate n 0 = fundamentalChain n := by rfl
    rw [h1] at hσ
    have h_support : Finsupp.support (fundamentalChain n) = {fundamentalSimplex n} := by
      dsimp only [fundamentalChain]
      ; simp
    rw [h_support] at hσ
    have hσ_eq : σ = fundamentalSimplex n := by simpa using hσ
    rw [hσ_eq]
    constructor
    · exact fundamentalSimplex_isAffine n
    · have h_img : simplexImage (fundamentalSimplex n) = stdSimplex ℝ (Fin (n + 1)) := by
        dsimp only [simplexImage, fundamentalSimplex]
        ext z
        simp only [Set.mem_range]
        constructor
        · rintro ⟨t, rfl⟩
          exact t.property
        · intro hz
          exact ⟨⟨z, hz⟩, rfl⟩
      rw [h_img]
      have h_diam_le_one : Metric.diam (stdSimplex ℝ (Fin (n + 1))) ≤ 1 := stdSimplex_diam_le_one n
      simpa using h_diam_le_one
  | succ k ih =>
    intro σ hσ
    have h1 : sdIterate n (k + 1) = sdMap n (sdIterate n k) := by rfl
    rw [h1] at hσ
    have h_sdMap_supp : Finsupp.support (sdMap n (sdIterate n k)) ⊆
        (Finsupp.support (sdIterate n k)).biUnion fun τ =>
          Finsupp.support ((sdIterate n k τ) • sdSimplex τ) :=
      Finsupp.support_sum
    have hσ_in : σ ∈ (Finsupp.support (sdIterate n k)).biUnion fun τ =>
        Finsupp.support ((sdIterate n k τ) • sdSimplex τ) :=
      h_sdMap_supp hσ
    have h_exists : ∃ (τ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
        τ ∈ Finsupp.support (sdIterate n k) ∧
        σ ∈ Finsupp.support (sdSimplex τ) := by
      simp only [Finset.mem_biUnion] at hσ_in
      rcases hσ_in with ⟨τ, hτ_supp, hσ_in'⟩
      have h4 : σ ∈ Finsupp.support (sdSimplex τ) := by
        have h5 : Finsupp.support ((sdIterate n k τ) • sdSimplex τ) ⊆
            Finsupp.support (sdSimplex τ) := Finsupp.support_smul
        exact h5 hσ_in'
      exact ⟨τ, hτ_supp, h4⟩
    rcases h_exists with ⟨τ, hτ_supp, hσ_sd⟩
    have hτ_ih := ih τ hτ_supp
    have hτ_affine : IsAffineSimplex τ := hτ_ih.1
    have hτ_diam : Metric.diam (simplexImage τ) ≤ ((n : ℝ) / (n + 1 : ℝ)) ^ k := hτ_ih.2
    have h_main : Metric.diam (simplexImage σ) ≤
        (n : ℝ) / (n + 1 : ℝ) * Metric.diam (simplexImage τ) :=
      sdSimplex_shrinks hτ_affine σ hσ_sd
    have hσ_affine : IsAffineSimplex σ := by
      rcases hτ_affine with ⟨A_τ, b_τ, hτ_eq⟩
      have h_push_supp2 : Finsupp.support (sdSimplex τ) ⊆
          (Finsupp.support (sd_fundamental n)).biUnion fun τ' =>
            Finsupp.support ((sd_fundamental n τ') • Finsupp.single
              (SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ') (1 : ℤ)) :=
        Finsupp.support_sum
      have hσ_in2 : σ ∈ (Finsupp.support (sd_fundamental n)).biUnion fun τ' =>
          Finsupp.support ((sd_fundamental n τ') • Finsupp.single
            (SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ') (1 : ℤ)) :=
        h_push_supp2 hσ_sd
      have h_exists2 : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
          τ' ∈ Finsupp.support (sd_fundamental n) ∧
          σ = SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ' := by
        simp only [Finset.mem_biUnion] at hσ_in2
        rcases hσ_in2 with ⟨τ', hτ'_supp, hσ_in3⟩
        have h4 : σ ∈ Finsupp.support (Finsupp.single
            (SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ') (1 : ℤ)) := by
          have h5 : Finsupp.support ((sd_fundamental n τ') • Finsupp.single
              (SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ') (1 : ℤ)) ⊆
              Finsupp.support (Finsupp.single
                (SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ') (1 : ℤ)) :=
            Finsupp.support_smul
          exact h5 hσ_in3
        have h6 : σ = SingularChain.pushforwardSimplex ⟨τ.val, τ.2⟩ τ' := by
          simpa [Finsupp.support_single] using h4
        exact ⟨τ', hτ'_supp, h6⟩
      rcases h_exists2 with ⟨τ', hτ'_supp, rfl⟩
      have hτ'_affine : IsAffineSimplex τ' := sd_fundamental_all_affine n τ' hτ'_supp
      exact pushforward_isAffine hτ'_affine τ.2 A_τ b_τ hτ_eq
    constructor
    · exact hσ_affine
    · calc
        Metric.diam (simplexImage σ)
          ≤ (n : ℝ) / (n + 1 : ℝ) * Metric.diam (simplexImage τ) := h_main
        _ ≤ (n : ℝ) / (n + 1 : ℝ) * (((n : ℝ) / (n + 1 : ℝ)) ^ k) := by gcongr
        _ = ((n : ℝ) / (n + 1 : ℝ)) ^ (k + 1) := by
          simp [pow_succ]
          ; ring

end IteratedMeshShrinking

-- ============================================
-- Geometric Small Chain Theorem
-- ============================================

section GeometricSmallChain

variable {X : Type*} [PseudoMetricSpace X]
variable {ι : Type*} {K : Set X}
variable (hK : IsCompact K)
variable (𝒰 : ι → Set X) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i)

open SingularChain

/-- Uniform continuity implies diameter shrinking:
    if `f` is uniformly continuous, then for any `δ > 0`, there exists `ε > 0`
    such that any bounded set of diameter `< ε` is mapped to a set of diameter `< δ`. -/
lemma uniformContinuous_diam_shrinking {Y : Type*} [PseudoMetricSpace Y]
    {f : Y → X} (hf : UniformContinuous f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (S : Set Y), Bornology.IsBounded S → Metric.diam S < ε → Metric.diam (f '' S) < δ := by
  have hδ2_pos : 0 < δ / 2 := by linarith
  rcases Metric.uniformContinuous_iff.mp hf (δ / 2) hδ2_pos with ⟨ε, hε_pos, hε⟩
  refine' ⟨ε, hε_pos, _⟩
  intro S hS_bdd h_diam_lt
  by_cases hS : S.Nonempty
  · have h_main : ∀ x ∈ f '' S, ∀ y ∈ f '' S, dist x y ≤ δ / 2 := by
      intro z1 hz1 z2 hz2
      rcases hz1 with ⟨u, hu, rfl⟩
      rcases hz2 with ⟨v, hv, rfl⟩
      have h_dist_uv : dist u v < ε := by
        have h : dist u v ≤ Metric.diam S := Metric.dist_le_diam_of_mem hS_bdd hu hv
        exact h.trans_lt h_diam_lt
      have h : dist (f u) (f v) < δ / 2 := hε h_dist_uv
      exact le_of_lt h
    have h_diam_le : Metric.diam (f '' S) ≤ δ / 2 :=
      Metric.diam_le_of_forall_dist_le (by linarith) h_main
    have h_final : Metric.diam (f '' S) < δ := by
      calc
        Metric.diam (f '' S) ≤ δ / 2 := h_diam_le
        _ < δ := by linarith
    exact h_final
  · have h_empty : f '' S = ∅ := by
      rw [Set.image_eq_empty.mpr]
      exact Set.not_nonempty_iff_eq_empty.mp hS
    rw [h_empty]
    simpa using hδ

/-- For any `ε > 0`, there exists `k : ℕ` such that `((n : ℝ) / (n + 1 : ℝ)) ^ k < ε`. -/
lemma exists_k_pow_lt (n : ℕ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ((n : ℝ) / (n + 1 : ℝ)) ^ k < ε := by
  have h1 : 0 < (n : ℝ) / (n + 1 : ℝ) := by positivity
  have h2 : (n : ℝ) / (n + 1 : ℝ) < 1 := by
    have h3 : (n : ℝ) < (n + 1 : ℝ) := by linarith
    have h4 : 0 < (n + 1 : ℝ) := by positivity
    exact (div_lt_one h4).mpr h3
  have h5 : ∃ k : ℕ, ((n : ℝ) / (n + 1 : ℝ)) ^ k < ε :=
    exists_pow_lt_of_lt_one hε h2
  exact h5

/-- **Geometric small chain theorem (single simplex version)**:
    For any singular n-simplex σ with image in K, there exists k such that
    sdᵏ(σ) is 𝒰-small. -/
theorem geometric_small_chain_single {n : ℕ} (hn : 0 < n)
    (hK : IsCompact K) (𝒰 : ι → Set X) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i)
    (σ : SingularSimplex X n) (hσ : Set.range σ.val ⊆ K) :
    ∃ k : ℕ, AllSmall 𝒰 ((sdMap n)^[k] (Finsupp.single σ (1 : ℤ))) := by
  classical
  -- Step 1: Get Lebesgue number δ
  have h_lebesgue : ∃ δ > 0, ∀ (A : Set X), Bornology.IsBounded A → A ∩ K ≠ ∅ →
      Metric.diam A < δ → ∃ i : ι, A ⊆ 𝒰 i := by
    rcases lebesgue_number_lemma_of_metric hK hU hcover with ⟨δ, hδ_pos, hδ⟩
    refine' ⟨δ, hδ_pos, _⟩
    intro A hA_bdd hA_inter_ne h_diam_lt
    have hA_inter_nonempty : (A ∩ K).Nonempty := Set.nonempty_iff_ne_empty.mpr hA_inter_ne
    rcases hA_inter_nonempty with ⟨x, hx⟩
    have hxA : x ∈ A := hx.1
    have hxK : x ∈ K := hx.2
    rcases hδ x hxK with ⟨i, hi⟩
    have hA_subset : A ⊆ Metric.ball x δ := by
      intro y hy
      have h_bdd : Bornology.IsBounded A := hA_bdd
      have h_dist_le : dist y x ≤ Metric.diam A := Metric.dist_le_diam_of_mem h_bdd hy hxA
      have h_dist : dist y x < δ := by
        calc
          dist y x ≤ Metric.diam A := h_dist_le
          _ < δ := h_diam_lt
      exact h_dist
    exact ⟨i, subset_trans hA_subset hi⟩
  rcases h_lebesgue with ⟨δ, hδ_pos, h_lebesgue'⟩
  -- Step 2: σ is uniformly continuous (domain is compact)
  have hσ_cont : Continuous σ.val := σ.property
  have hσ_uniform : UniformContinuous σ.val :=
    CompactSpace.uniformContinuous_of_continuous hσ_cont
  -- Step 3: Find ε > 0 such that diam(S) < ε ⇒ diam(σ.val '' S) < δ
  rcases uniformContinuous_diam_shrinking hσ_uniform hδ_pos with ⟨ε, hε_pos, hε⟩
  -- Step 4: Find k such that every simplex in sdᵏ(ιₙ) has diameter < ε
  have h_exists_k : ∃ k : ℕ, ∀ τ ∈ Finsupp.support (sdIterate n k),
      Metric.diam (simplexImage τ) < ε := by
    rcases exists_k_pow_lt n hn hε_pos with ⟨k, hk⟩
    refine' ⟨k, _⟩
    intro τ hτ
    have h_main : Metric.diam (simplexImage τ) ≤ ((n : ℝ) / (n + 1 : ℝ)) ^ k :=
      (iterated_mesh_shrinking n k τ hτ).2
    exact lt_of_le_of_lt h_main hk
  rcases h_exists_k with ⟨k, hk⟩
  -- Step 5: sdᵏ(σ) = σ_*(sdᵏ(ιₙ))
  have h_sd_sigma : (sdMap n)^[k] (Finsupp.single σ (1 : ℤ)) =
      pushforward ⟨σ.val, σ.property⟩ (sdIterate n k) := by
    have h1 : Finsupp.single σ (1 : ℤ) =
        pushforward ⟨σ.val, σ.property⟩ (fundamentalChain n) := by
      simp [fundamentalChain, pushforward]
      ; rfl
    rw [h1]
    have h2 : ∀ k : ℕ, (sdMap n)^[k] (pushforward ⟨σ.val, σ.property⟩ (fundamentalChain n)) =
        pushforward ⟨σ.val, σ.property⟩ (sdIterate n k) := by
      intro k
      induction k with
      | zero => simp [sdIterate, fundamentalChain]
      | succ k ih =>
        simp_all [sdIterate, Function.iterate_succ_apply', sdMap_pushforward]
    exact h2 k
  refine' ⟨k, _⟩
  rw [h_sd_sigma]
  -- Step 6: Every simplex in the pushforward has image ⊆ K and diameter < δ,
  -- hence is 𝒰-small
  intro τ hτ
  have h_exists : ∃ (τ' : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
      τ' ∈ Finsupp.support (sdIterate n k) ∧
      τ = pushforwardSimplex ⟨σ.val, σ.property⟩ τ' := by
    have h_push_supp : Finsupp.support (pushforward ⟨σ.val, σ.property⟩ (sdIterate n k)) ⊆
        (Finsupp.support (sdIterate n k)).biUnion fun τ' =>
          Finsupp.support ((sdIterate n k τ') • Finsupp.single
            (pushforwardSimplex ⟨σ.val, σ.property⟩ τ') (1 : ℤ)) :=
      Finsupp.support_sum
    have hτ_in : τ ∈ (Finsupp.support (sdIterate n k)).biUnion fun τ' =>
        Finsupp.support ((sdIterate n k τ') • Finsupp.single
          (pushforwardSimplex ⟨σ.val, σ.property⟩ τ') (1 : ℤ)) :=
      h_push_supp hτ
    simp only [Finset.mem_biUnion] at hτ_in
    rcases hτ_in with ⟨τ', hτ'_supp, hτ_in'⟩
    have h4 : τ ∈ Finsupp.support (Finsupp.single
        (pushforwardSimplex ⟨σ.val, σ.property⟩ τ') (1 : ℤ)) := by
      have h5 : Finsupp.support ((sdIterate n k τ') • Finsupp.single
          (pushforwardSimplex ⟨σ.val, σ.property⟩ τ') (1 : ℤ)) ⊆
          Finsupp.support (Finsupp.single
            (pushforwardSimplex ⟨σ.val, σ.property⟩ τ') (1 : ℤ)) :=
        Finsupp.support_smul
      exact h5 hτ_in'
    have h6 : τ = pushforwardSimplex ⟨σ.val, σ.property⟩ τ' := by
      simpa [Finsupp.support_single] using h4
    exact ⟨τ', hτ'_supp, h6⟩
  rcases h_exists with ⟨τ', hτ'_supp, rfl⟩
  have h_diam_lt : Metric.diam (simplexImage τ') < ε := hk τ' hτ'_supp
  have h_range_eq : Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val =
      σ.val '' (Set.range τ'.val) := by
    have h1 : (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val = σ.val ∘ τ'.val := by rfl
    rw [h1, Set.range_comp]
  have h_diam_range : Metric.diam (Set.range τ'.val) < ε := by
    have h_eq : Metric.diam (Set.range τ'.val) = Metric.diam (simplexImage τ') := by
      let f : {x // x ∈ stdSimplex ℝ (Fin (n + 1))} → (Fin (n + 1) → ℝ) := fun x => x.val
      have hf_isom : Isometry f := by
        intro x y
        rfl
      have h_img : f '' (Set.range τ'.val) = simplexImage τ' := by
        have h1 : f '' (Set.range τ'.val) = Set.range (f ∘ τ'.val) := by
          ext z
          simp only [Set.mem_image, Set.mem_range]
          constructor
          · rintro ⟨x, hx, rfl⟩
            rcases hx with ⟨y, rfl⟩
            refine' ⟨y, _⟩
            simp
          · rintro ⟨y, rfl⟩
            refine' ⟨τ'.val y, ⟨y, rfl⟩, _⟩
            simp
        rw [h1]
        rfl
      have h : Metric.diam (f '' (Set.range τ'.val)) = Metric.diam (Set.range τ'.val) :=
        hf_isom.diam_image (Set.range τ'.val)
      rw [h_img] at h
      exact h.symm
    rw [h_eq]
    exact h_diam_lt
  have h_bdd_range : Bornology.IsBounded (Set.range τ'.val) := by
    have h_compact : IsCompact (Set.range τ'.val) := isCompact_range τ'.property
    exact h_compact.isBounded
  have h_diam_image : Metric.diam (σ.val '' (Set.range τ'.val)) < δ :=
    hε (Set.range τ'.val) h_bdd_range h_diam_range
  have h_diam_image2 : Metric.diam (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val) < δ := by
    rw [h_range_eq]
    exact h_diam_image
  have h_img_subset_K : Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val ⊆ K := by
    have h1 : Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val ⊆ Set.range σ.val := by
      have h2 : (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val = σ.val ∘ τ'.val := by rfl
      rw [h2]
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨τ'.val x, rfl⟩
    calc
      Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val
        ⊆ Set.range σ.val := h1
      _ ⊆ K := hσ
  have h_bdd : Bornology.IsBounded (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val) := by
    have h_compact : IsCompact (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val) :=
      isCompact_range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').property
    exact h_compact.isBounded
  have h_inter_ne : (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val) ∩ K ≠ ∅ := by
    have h_nonempty : (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val).Nonempty :=
      Set.range_nonempty _
    have h_eq : (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val) ∩ K =
        Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val := by
      exact Set.inter_eq_left.mpr h_img_subset_K
    rw [h_eq]
    exact Set.nonempty_iff_ne_empty.mp h_nonempty
  have h_small : ∃ i : ι, Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val ⊆ 𝒰 i :=
    h_lebesgue' (Set.range (pushforwardSimplex ⟨σ.val, σ.property⟩ τ').val)
      h_bdd h_inter_ne h_diam_image2
  exact h_small

-- ============================================
-- Preservation lemmas for sd and T
-- ============================================

section Preservation

variable {X : Type*} [TopologicalSpace X]
variable {ι : Type*} {𝒰 : ι → Set X} {K : Set X}

open SingularChain

/-- The image of a pushforward simplex is contained in the range of f. -/
lemma pushforwardSimplex_image' {Y : Type*} [TopologicalSpace Y]
    (f : C(Y, X)) {n : ℕ} (σ : SingularSimplex Y n) :
    Set.range (pushforwardSimplex f σ).val ⊆ Set.range f := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact ⟨σ.val x, rfl⟩

/-- For any simplex τ in the support of `sdSimplex σ`,
    the image of τ is contained in the image of σ. -/
lemma sdSimplex_image_subset {n : ℕ} (σ : SingularSimplex X n) :
    ∀ τ ∈ Finsupp.support (sdSimplex σ), Set.range τ.val ⊆ Set.range σ.val := by
  have h1 : sdSimplex σ = pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n) := by rfl
  rw [h1]
  intro τ hτ
  have h_main : ∀ τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (sd_fundamental n)),
      Set.range τ.val ⊆ Set.range σ.val := by
    let P : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n → Prop :=
      fun c' => ∀ τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ c'),
        Set.range τ.val ⊆ Set.range σ.val
    have h_zero : P 0 := by
      simp [P]
      ; tauto
    have h_add : ∀ (ρ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n)
        (r : ℤ) (c' : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} n),
        ρ ∉ Finsupp.support c' → r ≠ 0 → P c' →
        P (Finsupp.single ρ r + c') := by
      intro ρ r c' hρ_notin hr ih
      dsimp only [P] at *
      have h_sum : pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r + c') =
          pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
          pushforward ⟨σ.val, σ.2⟩ c' :=
        pushforward_add ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) c'
      rw [h_sum]
      intro τ hτ
      by_cases h_left : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ c')
      · exact ih τ h_left
      · have h_right : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r)) := by
          have h9 : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
              pushforward ⟨σ.val, σ.2⟩ c') := hτ
          have h10 : (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
              pushforward ⟨σ.val, σ.2⟩ c') τ ≠ 0 :=
            Finsupp.mem_support_iff.mp h9
          have h11 : (pushforward ⟨σ.val, σ.2⟩ c') τ = 0 := by simpa using h_left
          have h12 : (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r)) τ ≠ 0 := by
            rw [Finsupp.add_apply, h11] at h10 ; simpa using h10
          exact Finsupp.mem_support_iff.mpr h12
        have h_smul : pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) =
            r • pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ)) := by
          have hsr : Finsupp.single ρ r = r • Finsupp.single ρ (1 : ℤ) := by
            simp [Finsupp.smul_single]
          rw [hsr]
          exact pushforward_smul ⟨σ.val, σ.2⟩ r (Finsupp.single ρ (1 : ℤ))
        rw [h_smul] at h_right
        have h_smul_supp : Finsupp.support (r • pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) ⊆
            Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) :=
          Finsupp.support_smul
        have hτ_in : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) :=
          h_smul_supp h_right
        have h_eq : τ = pushforwardSimplex ⟨σ.val, σ.2⟩ ρ := by
          simpa [pushforward, Finsupp.support_single] using hτ_in
        rw [h_eq]
        exact pushforwardSimplex_image' ⟨σ.val, σ.2⟩ ρ
    have hP : P (sd_fundamental n) := Finsupp.induction (sd_fundamental n) h_zero h_add
    exact hP
  exact h_main τ hτ

/-- sd preserves "image in K" property. -/
theorem sd_preserves_image (n : ℕ) (c : SingularChain ℤ X n)
    (h : ∀ σ ∈ Finsupp.support c, Set.range σ.val ⊆ K) :
    ∀ τ ∈ Finsupp.support (sdMap n c), Set.range τ.val ⊆ K := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    (∀ σ ∈ Finsupp.support c', Set.range σ.val ⊆ K) →
    (∀ τ ∈ Finsupp.support (sdMap n c'), Set.range τ.val ⊆ K)
  have h_zero : P 0 := by
    dsimp only [P]
    intro _
    simp [sdMap]
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ Finsupp.support c' → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' hσ_notin hr ih
    dsimp only [P] at *
    intro h_all
    have h_sum : sdMap n (Finsupp.single σ r + c') =
        sdMap n (Finsupp.single σ r) + sdMap n c' :=
      sdMap_add n (Finsupp.single σ r) c'
    rw [h_sum]
    have h_c'_img : ∀ τ ∈ Finsupp.support c', Set.range τ.val ⊆ K := by
      intro τ hτ
      have h_ne : c' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
      have h_contra : τ ≠ σ := by
        intro h_eq
        rw [h_eq] at h_ne
        exact Finsupp.mem_support_iff.not.mp hσ_notin h_ne
      have h_sum_ne : (Finsupp.single σ r + c') τ ≠ 0 := by
        have h4 : (Finsupp.single σ r) τ = 0 := by
          rw [Finsupp.single_apply_eq_zero]
          intro h_eq
          exfalso
          exact h_contra h_eq
        rw [Finsupp.add_apply, h4, zero_add]
        exact h_ne
      exact h_all τ (Finsupp.mem_support_iff.mpr h_sum_ne)
    have h_ih : ∀ τ ∈ Finsupp.support (sdMap n c'), Set.range τ.val ⊆ K := ih h_c'_img
    have hσ_in : σ ∈ Finsupp.support (Finsupp.single σ r + c') := by
      have h_coeff : (Finsupp.single σ r + c') σ = r := by
        have h1 : (Finsupp.single σ r + c') σ = (Finsupp.single σ r) σ + c' σ := Finsupp.add_apply _ _ _
        rw [h1]
        have h2 : (Finsupp.single σ r) σ = r := by simp
        have h3 : c' σ = 0 := by simpa [Finsupp.mem_support_iff] using hσ_notin
        rw [h2, h3, add_zero]
      have h_ne_zero : (Finsupp.single σ r + c') σ ≠ 0 := by
        rw [h_coeff]; exact hr
      exact Finsupp.mem_support_iff.mpr h_ne_zero
    have hσ_img : Set.range σ.val ⊆ K := h_all σ hσ_in
    have h_sdSimplex : sdMap n (Finsupp.single σ r) = r • sdSimplex σ := by
      have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
        simp [Finsupp.smul_single]
      rw [hsr, sdMap_smul n r (Finsupp.single σ (1 : ℤ))]
      ; congr
      ; simp [sdMap, Finsupp.sum_single_index]
    intro τ hτ
    by_cases h_left : τ ∈ Finsupp.support (sdMap n c')
    · exact h_ih τ h_left
    · have h_right : τ ∈ Finsupp.support (sdMap n (Finsupp.single σ r)) := by
        have h9 : τ ∈ Finsupp.support (sdMap n (Finsupp.single σ r) + sdMap n c') := hτ
        have h10 : (sdMap n (Finsupp.single σ r) + sdMap n c') τ ≠ 0 :=
          Finsupp.mem_support_iff.mp h9
        have h11 : (sdMap n c') τ = 0 := by simpa using h_left
        have h12 : (sdMap n (Finsupp.single σ r)) τ ≠ 0 := by
          rw [Finsupp.add_apply, h11] at h10 ; simpa using h10
        exact Finsupp.mem_support_iff.mpr h12
      rw [h_sdSimplex] at h_right
      have h_smul_supp : Finsupp.support (r • sdSimplex σ) ⊆ Finsupp.support (sdSimplex σ) :=
        Finsupp.support_smul
      have hτ_sd : τ ∈ Finsupp.support (sdSimplex σ) := h_smul_supp h_right
      have hτ_img : Set.range τ.val ⊆ Set.range σ.val := sdSimplex_image_subset σ τ hτ_sd
      exact subset_trans hτ_img hσ_img
  have hP : P c := Finsupp.induction c h_zero h_add
  exact hP h

/-- sd preserves 𝒰-small chains. -/
theorem sd_preserves_small (n : ℕ) {c : SingularChain ℤ X n}
    (h : AllSmall 𝒰 c) : AllSmall 𝒰 (sdMap n c) := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    AllSmall 𝒰 c' → AllSmall 𝒰 (sdMap n c')
  have h_zero : P 0 := by
    dsimp only [P]
    intro _
    simpa [sdMap] using allSmall_zero
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ Finsupp.support c' → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' hσ_notin hr ih
    dsimp only [P] at *
    intro h_all
    have h_sum : sdMap n (Finsupp.single σ r + c') =
        sdMap n (Finsupp.single σ r) + sdMap n c' :=
      sdMap_add n (Finsupp.single σ r) c'
    rw [h_sum]
    have h_c0_small : AllSmall 𝒰 c' := by
      intro τ hτ
      exact h_all τ (by
        have h_ne : c' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
        have h_contra : τ ≠ σ := by
          intro h_eq
          rw [h_eq] at h_ne
          exact Finsupp.mem_support_iff.not.mp hσ_notin h_ne
        have h_sum_ne : (Finsupp.single σ r + c') τ ≠ 0 := by
          have h4 : (Finsupp.single σ r) τ = 0 := by
            rw [Finsupp.single_apply_eq_zero]
            intro h_eq
            exfalso
            exact h_contra h_eq
          rw [Finsupp.add_apply, h4, zero_add]
          exact h_ne
        exact Finsupp.mem_support_iff.mpr h_sum_ne)
    have h_ih : AllSmall 𝒰 (sdMap n c') := ih h_c0_small
    have hσ_in : σ ∈ Finsupp.support (Finsupp.single σ r + c') := by
      have h_coeff : (Finsupp.single σ r + c') σ = r := by
        have h1 : (Finsupp.single σ r + c') σ = (Finsupp.single σ r) σ + c' σ := Finsupp.add_apply _ _ _
        rw [h1]
        have h2 : (Finsupp.single σ r) σ = r := by simp
        have h3 : c' σ = 0 := by simpa [Finsupp.mem_support_iff] using hσ_notin
        rw [h2, h3, add_zero]
      have h_ne_zero : (Finsupp.single σ r + c') σ ≠ 0 := by
        rw [h_coeff]; exact hr
      exact Finsupp.mem_support_iff.mpr h_ne_zero
    have hσ_small : IsSmallWithRespectTo 𝒰 σ := h_all σ hσ_in
    have h_sdSimplex : sdMap n (Finsupp.single σ r) = r • sdSimplex σ := by
      have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
        simp [Finsupp.smul_single]
      rw [hsr, sdMap_smul n r (Finsupp.single σ (1 : ℤ))]
      ; congr
      ; simp [sdMap, Finsupp.sum_single_index]
    rw [h_sdSimplex]
    have h_sdSimplex_small : AllSmall 𝒰 (sdSimplex σ) := by
      intro τ hτ
      rcases hσ_small with ⟨i, hi⟩
      have hτ_img : Set.range τ.val ⊆ Set.range σ.val := sdSimplex_image_subset σ τ hτ
      exact ⟨i, subset_trans hτ_img hi⟩
    have h_smul_small : AllSmall 𝒰 (r • sdSimplex σ) := allSmall_smul h_sdSimplex_small
    exact allSmall_add h_smul_small h_ih
  have hP : P c := Finsupp.induction c h_zero h_add
  exact hP h

/-- For any simplex τ in the support of `TSimplex σ`,
    the image of τ is contained in the image of σ. -/
lemma TSimplex_image_subset {n : ℕ} (σ : SingularSimplex X n) :
    ∀ τ ∈ Finsupp.support (TSimplex σ), Set.range τ.val ⊆ Set.range σ.val := by
  have h1 : TSimplex σ = pushforward ⟨σ.val, σ.2⟩ (T_fundamental n) := by rfl
  rw [h1]
  intro τ hτ
  have h_main : ∀ τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (T_fundamental n)),
      Set.range τ.val ⊆ Set.range σ.val := by
    let P : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} (n + 1) → Prop :=
      fun c' => ∀ τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ c'),
        Set.range τ.val ⊆ Set.range σ.val
    have h_zero : P 0 := by
      simp [P] ; tauto
    have h_add : ∀ (ρ : SingularSimplex {x // x ∈ stdSimplex ℝ (Fin (n + 1))} (n + 1))
        (r : ℤ) (c' : SingularChain ℤ {x // x ∈ stdSimplex ℝ (Fin (n + 1))} (n + 1)),
        ρ ∉ Finsupp.support c' → r ≠ 0 → P c' →
        P (Finsupp.single ρ r + c') := by
      intro ρ r c' hρ_notin hr ih
      dsimp only [P] at *
      have h_sum : pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r + c') =
          pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
          pushforward ⟨σ.val, σ.2⟩ c' :=
        pushforward_add ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) c'
      rw [h_sum]
      intro τ hτ
      by_cases h_left : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ c')
      · exact ih τ h_left
      · have h_right : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r)) := by
          have h9 : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
              pushforward ⟨σ.val, σ.2⟩ c') := hτ
          have h10 : (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) +
              pushforward ⟨σ.val, σ.2⟩ c') τ ≠ 0 :=
            Finsupp.mem_support_iff.mp h9
          have h11 : (pushforward ⟨σ.val, σ.2⟩ c') τ = 0 := by simpa using h_left
          have h12 : (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r)) τ ≠ 0 := by
            rw [Finsupp.add_apply, h11] at h10 ; simpa using h10
          exact Finsupp.mem_support_iff.mpr h12
        have h_smul : pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ r) =
            r • pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ)) := by
          have hsr : Finsupp.single ρ r = r • Finsupp.single ρ (1 : ℤ) := by
            simp [Finsupp.smul_single]
          rw [hsr]
          exact pushforward_smul ⟨σ.val, σ.2⟩ r (Finsupp.single ρ (1 : ℤ))
        rw [h_smul] at h_right
        have h_smul_supp : Finsupp.support (r • pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) ⊆
            Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) :=
          Finsupp.support_smul
        have hτ_in : τ ∈ Finsupp.support (pushforward ⟨σ.val, σ.2⟩ (Finsupp.single ρ (1 : ℤ))) :=
          h_smul_supp h_right
        have h_eq : τ = pushforwardSimplex ⟨σ.val, σ.2⟩ ρ := by
          simpa [pushforward, Finsupp.support_single] using hτ_in
        rw [h_eq]
        exact pushforwardSimplex_image' ⟨σ.val, σ.2⟩ ρ
    have hP : P (T_fundamental n) := Finsupp.induction (T_fundamental n) h_zero h_add
    exact hP
  exact h_main τ hτ

/-- T preserves 𝒰-small chains. -/
theorem T_preserves_small (n : ℕ) {c : SingularChain ℤ X n}
    (h : AllSmall 𝒰 c) : AllSmall 𝒰 (TMap n c) := by
  let P : SingularChain ℤ X n → Prop := fun c' =>
    AllSmall 𝒰 c' → AllSmall 𝒰 (TMap n c')
  have h_zero : P 0 := by
    dsimp only [P]
    intro _
    simpa [TMap] using allSmall_zero
  have h_add : ∀ (σ : SingularSimplex X n) (r : ℤ) (c' : SingularChain ℤ X n),
      σ ∉ Finsupp.support c' → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' hσ_notin hr ih
    dsimp only [P] at *
    intro h_all
    have h_sum : TMap n (Finsupp.single σ r + c') =
        TMap n (Finsupp.single σ r) + TMap n c' :=
      TMap_add n (Finsupp.single σ r) c'
    rw [h_sum]
    have h_c0_small : AllSmall 𝒰 c' := by
      intro τ hτ
      exact h_all τ (by
        have h_ne : c' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
        have h_contra : τ ≠ σ := by
          intro h_eq
          rw [h_eq] at h_ne
          exact Finsupp.mem_support_iff.not.mp hσ_notin h_ne
        have h_sum_ne : (Finsupp.single σ r + c') τ ≠ 0 := by
          have h4 : (Finsupp.single σ r) τ = 0 := by
            rw [Finsupp.single_apply_eq_zero]
            intro h_eq
            exfalso
            exact h_contra h_eq
          rw [Finsupp.add_apply, h4, zero_add]
          exact h_ne
        exact Finsupp.mem_support_iff.mpr h_sum_ne)
    have h_ih : AllSmall 𝒰 (TMap n c') := ih h_c0_small
    have hσ_in : σ ∈ Finsupp.support (Finsupp.single σ r + c') := by
      have h_coeff : (Finsupp.single σ r + c') σ = r := by
        have h1 : (Finsupp.single σ r + c') σ = (Finsupp.single σ r) σ + c' σ := Finsupp.add_apply _ _ _
        rw [h1]
        have h2 : (Finsupp.single σ r) σ = r := by simp
        have h3 : c' σ = 0 := by simpa [Finsupp.mem_support_iff] using hσ_notin
        rw [h2, h3, add_zero]
      have h_ne_zero : (Finsupp.single σ r + c') σ ≠ 0 := by
        rw [h_coeff]; exact hr
      exact Finsupp.mem_support_iff.mpr h_ne_zero
    have hσ_small : IsSmallWithRespectTo 𝒰 σ := h_all σ hσ_in
    have h_TSimplex : TMap n (Finsupp.single σ r) = r • TSimplex σ := by
      have hsr : Finsupp.single σ r = r • Finsupp.single σ (1 : ℤ) := by
        simp [Finsupp.smul_single]
      rw [hsr, TMap_smul n r (Finsupp.single σ (1 : ℤ))]
      ; congr
      ; simp [TMap, Finsupp.sum_single_index]
    rw [h_TSimplex]
    have h_TSimplex_small : AllSmall 𝒰 (TSimplex σ) := by
      intro τ hτ
      rcases hσ_small with ⟨i, hi⟩
      have hτ_img : Set.range τ.val ⊆ Set.range σ.val := TSimplex_image_subset σ τ hτ
      exact ⟨i, subset_trans hτ_img hi⟩
    have h_smul_small : AllSmall 𝒰 (r • TSimplex σ) := allSmall_smul h_TSimplex_small
    exact allSmall_add h_smul_small h_ih
  have hP : P c := Finsupp.induction c h_zero h_add
  exact hP h

end Preservation

-- ============================================
-- Homological Small Chain Theorem
-- ============================================

section HomologicalSmallChain

variable {X : Type*} [PseudoMetricSpace X]
variable {ι : Type*} {K : Set X}
variable (hK : IsCompact K)
variable (𝒰 : ι → Set X) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i)

open SingularChain

-- ============================================
-- Iterated subdivision and chain homotopy
-- ============================================

/-- Iterated barycentric subdivision: sdᵏ applied to c. -/
def sdIter (k n : ℕ) (c : SingularChain ℤ X n) : SingularChain ℤ X n :=
  (sdMap n)^[k] c

/-- sdIter (k+1) = sdMap ∘ sdIter k. -/
lemma sdIter_succ (k n : ℕ) (c : SingularChain ℤ X n) :
    sdIter (k + 1) n c = sdMap n (sdIter k n c) := by
  simp [sdIter, Function.iterate_succ_apply']

/-- Iterated chain homotopy T_k with d(T_k) + T_k(d) = sdᵏ - id. -/
def TIter (k n : ℕ) (c : SingularChain ℤ X n) : SingularChain ℤ X (n + 1) :=
  Nat.recOn k (0 : SingularChain ℤ X (n + 1))
    (fun i acc => acc + TMap n (sdIter i n c))

/-- sdIter preserves addition. -/
lemma sdIter_add (k n : ℕ) (c1 c2 : SingularChain ℤ X n) :
    sdIter k n (c1 + c2) = sdIter k n c1 + sdIter k n c2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : sdIter (k + 1) n (c1 + c2) = sdMap n (sdIter k n (c1 + c2)) :=
      sdIter_succ k n (c1 + c2)
    have h2 : sdIter (k + 1) n c1 + sdIter (k + 1) n c2 =
        sdMap n (sdIter k n c1) + sdMap n (sdIter k n c2) := by
      rw [sdIter_succ k n c1, sdIter_succ k n c2]
    rw [h1, h2, ih, sdMap_add n]

/-- sdIter preserves scalar multiplication. -/
lemma sdIter_smul (k n : ℕ) (a : ℤ) (c : SingularChain ℤ X n) :
    sdIter k n (a • c) = a • sdIter k n c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : sdIter (k + 1) n (a • c) = sdMap n (sdIter k n (a • c)) :=
      sdIter_succ k n (a • c)
    rw [h1, ih, sdMap_smul n a (sdIter k n c)]
    have h_right : a • sdMap n (sdIter k n c) = a • sdIter (k + 1) n c := by
      rw [sdIter_succ k n c]
    exact h_right

/-- sdIter commutes with d (sd is a chain map, iterated). -/
lemma sdIter_comm_d (k n : ℕ) (c : SingularChain ℤ X (n + 1)) :
    sdIter k n (d n c) = d n (sdIter k (n + 1) c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : sdIter (k + 1) n (d n c) = sdMap n (sdIter k n (d n c)) :=
      sdIter_succ k n (d n c)
    have h2 : sdIter (k + 1) (n + 1) c = sdMap (n + 1) (sdIter k (n + 1) c) :=
      sdIter_succ k (n + 1) c
    rw [h1, h2]
    rw [ih]
    exact (sd_chainMap n (sdIter k (n + 1) c)).symm

/-- TIter preserves addition. -/
lemma TIter_add (k n : ℕ) (c1 c2 : SingularChain ℤ X n) :
    TIter k n (c1 + c2) = TIter k n c1 + TIter k n c2 := by
  induction k with
  | zero =>
    simp [TIter]
  | succ k ih =>
    have h1 : TIter (k + 1) n (c1 + c2) =
        TIter k n (c1 + c2) + TMap n (sdIter k n (c1 + c2)) := by rfl
    have h2 : TIter (k + 1) n c1 + TIter (k + 1) n c2 =
        (TIter k n c1 + TMap n (sdIter k n c1)) +
        (TIter k n c2 + TMap n (sdIter k n c2)) := by rfl
    rw [h1, h2, ih, sdIter_add k n c1 c2, TMap_add n]
    ; abel

/-- sdIter of zero is zero. -/
lemma sdIter_zero (k n : ℕ) : sdIter k n (0 : SingularChain ℤ X n) = 0 := by
  induction k with
  | zero =>
    simp [sdIter]
  | succ k ih =>
    have h1 : sdIter (k + 1) n (0 : SingularChain ℤ X n) =
        sdMap n (sdIter k n (0 : SingularChain ℤ X n)) :=
      sdIter_succ k n (0 : SingularChain ℤ X n)
    rw [h1, ih]
    have h2 : sdMap n (0 : SingularChain ℤ X n) = 0 := by
      have h := sdMap_add n (0 : SingularChain ℤ X n) (0 : SingularChain ℤ X n)
      simpa using h
    exact h2

/-- TIter of zero is zero. -/
lemma TIter_zero (k n : ℕ) : TIter k n (0 : SingularChain ℤ X n) = 0 := by
  induction k with
  | zero =>
    simp [TIter]
  | succ k ih =>
    have h1 : TIter (k + 1) n (0 : SingularChain ℤ X n) =
        TIter k n (0 : SingularChain ℤ X n) + TMap n (sdIter k n (0 : SingularChain ℤ X n)) := by rfl
    rw [h1, ih, sdIter_zero k n]
    have h2 : TMap n (0 : SingularChain ℤ X n) = 0 := by
      have h := TMap_add n (0 : SingularChain ℤ X n) (0 : SingularChain ℤ X n)
      simpa using h
    rw [h2] ; abel

/-- Iterated chain homotopy formula: d(T_k(c)) + T_k(d(c)) = sdᵏ(c) - c. -/
lemma iterated_chainHomotopy (k n : ℕ) (c : SingularChain ℤ X (n + 1)) :
    d (n + 1) (TIter k (n + 1) c) + TIter k n (d n c) =
    sdIter k (n + 1) c - c := by
  induction k with
  | zero =>
    have h_d_zero : d (n + 1) (0 : SingularChain ℤ X (n + 2)) = 0 := by
      have h := d_add (n + 1) (0 : SingularChain ℤ X (n + 2)) (0 : SingularChain ℤ X (n + 2))
      simpa using h
    simp [TIter, sdIter, h_d_zero]
  | succ k ih =>
    have hT1 : TIter (k + 1) (n + 1) c =
        TIter k (n + 1) c + TMap (n + 1) (sdIter k (n + 1) c) := by rfl
    have hT2 : TIter (k + 1) n (d n c) =
        TIter k n (d n c) + TMap n (sdIter k n (d n c)) := by rfl
    have hsd : sdIter (k + 1) (n + 1) c =
        sdMap (n + 1) (sdIter k (n + 1) c) :=
      sdIter_succ k (n + 1) c
    have h_d_add1 : d (n + 1) (TIter (k + 1) (n + 1) c) =
        d (n + 1) (TIter k (n + 1) c) +
        d (n + 1) (TMap (n + 1) (sdIter k (n + 1) c)) := by
      rw [hT1, d_add (n + 1)]
    have h5 : d (n + 1) (TMap (n + 1) (sdIter k (n + 1) c)) +
        TMap n (d n (sdIter k (n + 1) c)) =
        sdMap (n + 1) (sdIter k (n + 1) c) - sdIter k (n + 1) c :=
      chainHomotopy n (sdIter k (n + 1) c)
    have h6 : sdIter k n (d n c) = d n (sdIter k (n + 1) c) :=
      sdIter_comm_d k n c
    have h_goal : d (n + 1) (TIter (k + 1) (n + 1) c) + TIter (k + 1) n (d n c) =
        sdIter (k + 1) (n + 1) c - c := by
      rw [h_d_add1, hT2]
      have h_step : d (n + 1) (TIter k (n + 1) c) +
          d (n + 1) (TMap (n + 1) (sdIter k (n + 1) c)) +
          (TIter k n (d n c) + TMap n (sdIter k n (d n c))) =
          (d (n + 1) (TIter k (n + 1) c) + TIter k n (d n c)) +
          (d (n + 1) (TMap (n + 1) (sdIter k (n + 1) c)) +
            TMap n (sdIter k n (d n c))) := by abel
      rw [h_step]
      rw [ih]
      have h7 : TMap n (sdIter k n (d n c)) = TMap n (d n (sdIter k (n + 1) c)) := by
        rw [sdIter_comm_d k n c]
      rw [h7, h5, hsd] ; abel
    exact h_goal

/-- sdIter preserves 𝒰-small chains. -/
lemma sdIter_preserves_small (k n : ℕ) {c : SingularChain ℤ X n}
    (h : AllSmall 𝒰 c) : AllSmall 𝒰 (sdIter k n c) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have h1 : AllSmall 𝒰 (sdIter k n c) := ih
    have h2 : AllSmall 𝒰 (sdMap n (sdIter k n c)) := sd_preserves_small n h1
    have h3 : sdIter (k + 1) n c = sdMap n (sdIter k n c) := sdIter_succ k n c
    rw [h3]
    exact h2

/-- TIter preserves 𝒰-small chains. -/
lemma TIter_preserves_small (k n : ℕ) {c : SingularChain ℤ X n}
    (h : AllSmall 𝒰 c) : AllSmall 𝒰 (TIter k n c) := by
  induction k with
  | zero =>
    simpa [TIter] using allSmall_zero
  | succ k ih =>
    have h1 : AllSmall 𝒰 (TIter k n c) := ih
    have h2 : AllSmall 𝒰 (sdIter k n c) := by
      exact sdIter_preserves_small 𝒰 k n (c := c) h
    have h3 : AllSmall 𝒰 (TMap n (sdIter k n c)) := T_preserves_small n h2
    have h4 : TIter (k + 1) n c = TIter k n c + TMap n (sdIter k n c) := by rfl
    rw [h4]
    exact allSmall_add h1 h3

/-- sdIter preserves "image in K" property. -/
lemma sdIter_preserves_image (k n : ℕ) {c : SingularChain ℤ X n}
    (h : ∀ σ ∈ Finsupp.support c, Set.range σ.val ⊆ K) :
    ∀ τ ∈ Finsupp.support (sdIter k n c), Set.range τ.val ⊆ K := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have h1 : ∀ τ ∈ Finsupp.support (sdIter k n c), Set.range τ.val ⊆ K := ih
    have h2 : ∀ τ ∈ Finsupp.support (sdMap n (sdIter k n c)), Set.range τ.val ⊆ K :=
      sd_preserves_image n (sdIter k n c) h1
    have h3 : sdIter (k + 1) n c = sdMap n (sdIter k n c) :=
      sdIter_succ k n c
    rw [h3]
    exact h2

-- ============================================
-- Finite chain geometric small chain theorem
-- ============================================

/-- Finite chain version of geometric small chain theorem:
    for any chain c with all images in K, there exists k such that sdᵏ(c) is 𝒰-small. -/
theorem geometric_small_chain_finite (n : ℕ) (hn : 0 < n)
    (hK : IsCompact K) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i)
    (c : SingularChain ℤ X n)
    (hc : ∀ σ ∈ Finsupp.support c, Set.range σ.val ⊆ K) :
    ∃ k : ℕ, AllSmall 𝒰 (sdIter k n c) := by
  classical
  let S := Finsupp.support c
  have h_induction : ∀ (s : Finset (SingularSimplex X n))
      (c' : SingularChain ℤ X n),
      Finsupp.support c' ⊆ s →
      (∀ σ ∈ Finsupp.support c', Set.range σ.val ⊆ K) →
      ∃ k : ℕ, AllSmall 𝒰 (sdIter k n c') := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro c' hsub _
      have h_c_zero : c' = 0 := by
        simpa [Finsupp.support_eq_empty] using hsub
      rw [h_c_zero]
      refine' ⟨0, _⟩
      simpa [sdIter] using allSmall_zero
    | @insert σ s hσ_notin_s ih =>
      intro c' hsub hc'
      by_cases hσ_in : σ ∈ Finsupp.support c'
      · -- σ is in the support of c'
        let a : ℤ := c' σ
        let c'' : SingularChain ℤ X n := c' - a • Finsupp.single σ (1 : ℤ)
        have h_c''_σ : c'' σ = 0 := by
          simp [c''] ; ring
        have h_support_c'' : Finsupp.support c'' ⊆ s := by
          intro τ hτ
          have h_ne_zero : c'' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
          by_cases h_eq : τ = σ
          · rw [h_eq] at h_ne_zero
            exfalso
            exact h_ne_zero h_c''_σ
          · have h_c_τ_ne_zero : c' τ ≠ 0 := by
              have h_eq2 : c'' τ = c' τ - a * (Finsupp.single σ (1 : ℤ)) τ := by rfl
              rw [h_eq2] at h_ne_zero
              by_contra h_contra
              have h_single_zero : (Finsupp.single σ (1 : ℤ)) τ = 0 := by
                exact Finsupp.single_eq_of_ne h_eq
              rw [h_contra, h_single_zero] at h_ne_zero
              ; simp at h_ne_zero
            have h3 : τ ∈ Finsupp.support c' := Finsupp.mem_support_iff.mpr h_c_τ_ne_zero
            have h4 : τ ∈ insert σ s := hsub h3
            have h5 : τ = σ ∨ τ ∈ s := by
              simpa [Finset.mem_insert] using h4
            cases h5 with
            | inl h5 => exfalso; exact h_eq h5
            | inr h5 => exact h5
        have h_images_c'' : ∀ τ ∈ Finsupp.support c'', Set.range τ.val ⊆ K := by
          intro τ hτ
          have h_ne_zero : c'' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
          have h_c_τ_ne_zero : c' τ ≠ 0 := by
            have h_eq2 : c'' τ = c' τ - a * (Finsupp.single σ (1 : ℤ)) τ := by rfl
            rw [h_eq2] at h_ne_zero
            by_cases h_case : τ = σ
            · rw [h_case] at h_ne_zero
              have h_cσ : c' σ = a := by dsimp only [a]
              rw [h_cσ] at h_ne_zero
              simp at h_ne_zero
            · by_contra h_contra
              have h_single_zero : (Finsupp.single σ (1 : ℤ)) τ = 0 := by
                exact Finsupp.single_eq_of_ne h_case
              rw [h_contra, h_single_zero] at h_ne_zero
              ; simp at h_ne_zero
          have h3 : τ ∈ Finsupp.support c' := Finsupp.mem_support_iff.mpr h_c_τ_ne_zero
          exact hc' τ h3
        rcases ih c'' h_support_c'' h_images_c'' with ⟨k1, hk1⟩
        have hσ_image : Set.range σ.val ⊆ K := hc' σ hσ_in
        rcases geometric_small_chain_single hn hK 𝒰 hU hcover σ hσ_image with ⟨k2, hk2⟩
        have hk2'_eq : AllSmall 𝒰 (sdIter k2 n (Finsupp.single σ (1 : ℤ))) := by
          have h_eq : (sdMap n)^[k2] (Finsupp.single σ (1 : ℤ)) = sdIter k2 n (Finsupp.single σ (1 : ℤ)) := by
            rfl
          rw [h_eq] at hk2
          exact hk2
        let k := max k1 k2
        have hk1' : k1 ≤ k := le_max_left k1 k2
        have hk2' : k2 ≤ k := le_max_right k1 k2
        have h_sdIter_add_iter : ∀ (k1 m : ℕ) (c0 : SingularChain ℤ X n),
            sdIter (k1 + m) n c0 = sdIter m n (sdIter k1 n c0) := by
          intro k1 m c0
          induction m with
          | zero =>
            simp ; rfl
          | succ m ih2 =>
            have h1 : sdIter (k1 + (m + 1)) n c0 = sdMap n (sdIter (k1 + m) n c0) := by
              have h_succ : k1 + (m + 1) = (k1 + m) + 1 := by omega
              rw [h_succ]
              exact sdIter_succ (k1 + m) n c0
            have h2 : sdIter (m + 1) n (sdIter k1 n c0) =
                sdMap n (sdIter m n (sdIter k1 n c0)) :=
              sdIter_succ m n (sdIter k1 n c0)
            rw [h1, h2, ih2]
        have h_forward : ∀ (k1 : ℕ) (c0 : SingularChain ℤ X n),
            k1 ≤ k →
            AllSmall 𝒰 (sdIter k1 n c0) →
            AllSmall 𝒰 (sdIter k n c0) := by
          intro k1 c0 h_le h_small
          have h_exists : ∃ m : ℕ, k = k1 + m := by
            refine' ⟨k - k1, _⟩
            omega
          rcases h_exists with ⟨m, hm⟩
          rw [hm]
          rw [h_sdIter_add_iter k1 m c0]
          exact sdIter_preserves_small 𝒰 m n (c := sdIter k1 n c0) h_small
        have h_small1 : AllSmall 𝒰 (sdIter k n c'') :=
          h_forward k1 c'' hk1' hk1
        have h_small2 : AllSmall 𝒰 (sdIter k n (Finsupp.single σ (1 : ℤ))) :=
          h_forward k2 (Finsupp.single σ (1 : ℤ)) hk2' hk2
        have h_small3 : AllSmall 𝒰 (sdIter k n (a • Finsupp.single σ (1 : ℤ))) := by
          have h_eq : sdIter k n (a • Finsupp.single σ (1 : ℤ)) =
              a • sdIter k n (Finsupp.single σ (1 : ℤ)) :=
            sdIter_smul k n a (Finsupp.single σ (1 : ℤ))
          rw [h_eq]
          exact allSmall_smul h_small2
        have h_c_eq : c' = c'' + a • Finsupp.single σ (1 : ℤ) := by
          dsimp only [c''] ; abel
        have h_small4 : AllSmall 𝒰 (sdIter k n c') := by
          rw [h_c_eq]
          rw [sdIter_add k n c'' (a • Finsupp.single σ (1 : ℤ))]
          exact allSmall_add h_small1 h_small3
        exact ⟨k, h_small4⟩
      · -- σ is not in the support of c'
        have h_support_sub : Finsupp.support c' ⊆ s := by
          intro τ hτ
          have h4 : τ ∈ (insert σ s : Finset (SingularSimplex X n)) := hsub hτ
          have h5 : τ = σ ∨ τ ∈ s := by
            simpa [Finset.mem_insert] using h4
          cases h5 with
          | inl h5 =>
            exfalso
            have h_contra : σ ∈ Finsupp.support c' := by
              rw [←h5] ; exact hτ
            exact hσ_in h_contra
          | inr h5 => exact h5
        exact ih c' h_support_sub hc'
  exact h_induction S c (by simp [S]) hc

-- ============================================
-- Small chains subcomplex
-- ============================================

/-- The subcomplex of 𝒰-small chains. -/
def SmallChains (n : ℕ) :=
  { c : SingularChain ℤ X n // AllSmall 𝒰 c }

/-- Inclusion of small chains into all chains. -/
def small_inclusion (n : ℕ) : SmallChains 𝒰 n → SingularChain ℤ X n :=
  fun c => c.val

-- ============================================
-- Homological small chain theorem
-- ============================================

/-- **Small chain theorem (homological version)**.

    The inclusion of 𝒰-small chains into all chains induces an isomorphism
    on homology (surjectivity and injectivity). -/
theorem small_chain_homological (n : ℕ) (hn : 0 < n)
    (hK : IsCompact K) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i) :
    -- Surjectivity on homology: every cycle with image in K is homologous to a small cycle
    (∀ (z : SingularChain ℤ X (n + 1)),
      (∀ σ ∈ Finsupp.support z, Set.range σ.val ⊆ K) →
      d n z = 0 →
      ∃ (z' : SmallChains 𝒰 (n + 1)) (b : SingularChain ℤ X (n + 2)),
        z - small_inclusion 𝒰 (n + 1) z' = d (n + 1) b)
    ∧
    -- Injectivity on homology: if a small cycle is a boundary in the full complex,
    -- then it is a boundary in the small complex
    (∀ (z' : SmallChains 𝒰 (n + 1)) (b : SingularChain ℤ X (n + 2)),
      (∀ τ ∈ Finsupp.support b, Set.range τ.val ⊆ K) →
      small_inclusion 𝒰 (n + 1) z' = d (n + 1) b →
      ∃ (b' : SmallChains 𝒰 (n + 2)),
        d (n + 1) (small_inclusion 𝒰 (n + 2) b') = small_inclusion 𝒰 (n + 1) z') := by
  classical
  have h_d_neg : ∀ n (c : SingularChain ℤ X (n + 1)),
      d n (-c) = -d n c := by
    intro n c
    have h1 : d n (c + (-c)) = d n c + d n (-c) := d_add n c (-c)
    have h2 : c + (-c) = (0 : SingularChain ℤ X (n + 1)) := by
      ext x; simp
    rw [h2] at h1
    have h3 : d n (0 : SingularChain ℤ X (n + 1)) = 0 := by
      have h4 := d_add n (0 : SingularChain ℤ X (n + 1)) (0 : SingularChain ℤ X (n + 1))
      simpa using h4
    rw [h3] at h1
    have h4 : d n c + d n (-c) = 0 := h1.symm
    have h5 : d n (-c) + d n c = 0 := by
      rw [add_comm] ; exact h4
    exact eq_neg_of_add_eq_zero_left h5
  have h_surj : ∀ (z : SingularChain ℤ X (n + 1)),
      (∀ σ ∈ Finsupp.support z, Set.range σ.val ⊆ K) →
      d n z = 0 →
      ∃ (z' : SmallChains 𝒰 (n + 1)) (b : SingularChain ℤ X (n + 2)),
        z - small_inclusion 𝒰 (n + 1) z' = d (n + 1) b := by
    intro z hz_images hz_cycle
    rcases geometric_small_chain_finite (𝒰 := 𝒰) (n := n + 1) (hn := by linarith) (hK := hK) (hU := hU) (hcover := hcover) (c := z) (hc := hz_images) with ⟨k, hk_small⟩
    let z' : SmallChains 𝒰 (n + 1) := ⟨sdIter k (n + 1) z, hk_small⟩
    have h_homotopy : d (n + 1) (TIter k (n + 1) z) + TIter k n (d n z) =
        sdIter k (n + 1) z - z :=
      iterated_chainHomotopy k n z
    have h_dz_zero : d n z = 0 := hz_cycle
    have h_T_dz_zero : TIter k n (d n z) = 0 := by
      rw [h_dz_zero]
      exact TIter_zero k n
    have h_eq1 : d (n + 1) (TIter k (n + 1) z) = sdIter k (n + 1) z - z := by
      rw [h_T_dz_zero] at h_homotopy
      simpa using h_homotopy
    have h_d_neg' : d (n + 1) (-TIter k (n + 1) z) = -d (n + 1) (TIter k (n + 1) z) :=
      h_d_neg (n + 1) (TIter k (n + 1) z)
    have h_eq2 : z - sdIter k (n + 1) z = d (n + 1) (-TIter k (n + 1) z) := by
      rw [h_d_neg']
      rw [h_eq1] ; abel
    refine' ⟨z', -TIter k (n + 1) z, _⟩
    simpa [z', small_inclusion] using h_eq2
  have h_inj : ∀ (z' : SmallChains 𝒰 (n + 1)) (b : SingularChain ℤ X (n + 2)),
      (∀ τ ∈ Finsupp.support b, Set.range τ.val ⊆ K) →
      small_inclusion 𝒰 (n + 1) z' = d (n + 1) b →
      ∃ (b' : SmallChains 𝒰 (n + 2)),
        d (n + 1) (small_inclusion 𝒰 (n + 2) b') = small_inclusion 𝒰 (n + 1) z' := by
    intro z' b hb_images h_eq
    have h_dz' : d n (small_inclusion 𝒰 (n + 1) z') = 0 := by
      rw [h_eq]
      exact d_squared n b
    rcases geometric_small_chain_finite (𝒰 := 𝒰) (n := n + 2) (hn := by linarith) (hK := hK) (hU := hU) (hcover := hcover) (c := b) (hc := hb_images) with ⟨k, hk_b_small⟩
    have h_sdb_small : AllSmall 𝒰 (sdIter k (n + 2) b) := hk_b_small
    have h_z'_small : AllSmall 𝒰 (small_inclusion 𝒰 (n + 1) z') := z'.property
    have h_Tz'_small : AllSmall 𝒰 (TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) :=
      TIter_preserves_small 𝒰 k (n + 1) (c := small_inclusion 𝒰 (n + 1) z') h_z'_small
    have h_b'_small : AllSmall 𝒰
        (sdIter k (n + 2) b - TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) :=
      allSmall_sub h_sdb_small h_Tz'_small
    let b' : SmallChains 𝒰 (n + 2) :=
      ⟨sdIter k (n + 2) b - TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z'), h_b'_small⟩
    have h_sd_d_comm' : sdIter k (n + 1) (d (n + 1) b) =
        d (n + 1) (sdIter k (n + 2) b) :=
      sdIter_comm_d k (n + 1) b
    have h1 : sdIter k (n + 1) (small_inclusion 𝒰 (n + 1) z') =
        d (n + 1) (sdIter k (n + 2) b) := by
      rw [←h_sd_d_comm', h_eq]
    have h_homotopy_z' : d (n + 1) (TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) +
        TIter k n (d n (small_inclusion 𝒰 (n + 1) z')) =
        sdIter k (n + 1) (small_inclusion 𝒰 (n + 1) z') - small_inclusion 𝒰 (n + 1) z' :=
      iterated_chainHomotopy k n (small_inclusion 𝒰 (n + 1) z')
    have h_T_dz'_zero : TIter k n (d n (small_inclusion 𝒰 (n + 1) z')) = 0 := by
      rw [h_dz']
      exact TIter_zero k n
    have h2 : d (n + 1) (TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) =
        sdIter k (n + 1) (small_inclusion 𝒰 (n + 1) z') - small_inclusion 𝒰 (n + 1) z' := by
      rw [h_T_dz'_zero] at h_homotopy_z'
      simpa using h_homotopy_z'
    have h_d_sub : d (n + 1) (sdIter k (n + 2) b - TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) =
        d (n + 1) (sdIter k (n + 2) b) - d (n + 1) (TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) := by
      let x := sdIter k (n + 2) b
      let y := TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')
      have h3 : d (n + 1) (x - y) + d (n + 1) y = d (n + 1) x := by
        have h4 : d (n + 1) ((x - y) + y) = d (n + 1) (x - y) + d (n + 1) y :=
          d_add (n + 1) (x - y) y
        have h5 : (x - y) + y = x := by abel
        rw [h5] at h4
        exact h4.symm
      have h6 : d (n + 1) (x - y) = d (n + 1) x - d (n + 1) y := by
        have h3' : d (n + 1) (x - y) + d (n + 1) y = d (n + 1) x := h3
        have h_neg : d (n + 1) (x - y) = d (n + 1) x - d (n + 1) y := by
          calc
            d (n + 1) (x - y)
              = d (n + 1) (x - y) + d (n + 1) y - d (n + 1) y := by
                simp
            _ = d (n + 1) x - d (n + 1) y := by
                rw [h3']
        exact h_neg
      exact h6
    have h_main : d (n + 1) (small_inclusion 𝒰 (n + 2) b') = small_inclusion 𝒰 (n + 1) z' := by
      simp only [b', small_inclusion]
      have h_goal : d (n + 1) (sdIter k (n + 2) b - TIter k (n + 1) (small_inclusion 𝒰 (n + 1) z')) =
          small_inclusion 𝒰 (n + 1) z' := by
        rw [h_d_sub]
        rw [h1.symm, h2] ; abel
      exact h_goal
    exact ⟨b', h_main⟩
  exact ⟨h_surj, h_inj⟩

end HomologicalSmallChain

end GeometricSmallChain
section MathlibComparison

/-!
## Comparison with Mathlib's singular chain complex

We establish a comparison between our Finsupp-based singular chains and
Mathlib's singular chain complex, then transfer sd and T to Mathlib's setting.

We work in `AddCommGrpCat` (the category of abelian groups) with coefficients
in `ℤ`. This is equivalent to `ModuleCat ℤ` but has better `HasCoproducts`
instance support.

We work in `Type` (universe 0) which is sufficient for the Jordan-Brouwer
theorem (about `EuclideanSpace ℝ (Fin d)`).
-/

open CategoryTheory Limits Simplicial SSet
open TopCat (toSSet)

/-- Mathlib's singular simplicial set of a topological space X. -/
def singularSSet (X : Type) [TopologicalSpace X] : SSet :=
  toSSet.obj (TopCat.of X)

/-- Equivalence between Mathlib's n-simplices and our `SingularSimplex X n`. -/
def singularSimplexEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    (singularSSet X _⦋n⦌) ≃ SingularSimplex X n := by
  let e : (singularSSet X _⦋n⦌) ≃
      ContinuousMap (stdSimplex ℝ (Fin (n + 1))) (TopCat.of X) :=
    TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op (SimplexCategory.mk n))
  exact e.trans (Equiv.mk
    (fun f => ⟨f, f.continuous⟩)
    (fun σ => ⟨σ.val, σ.property⟩)
    (by intro σ; simp ; rfl)
    (by intro f; simp [SingularSimplex] ))

/-- The equivalence commutes with face maps. -/
lemma singularSimplexEquiv_face (X : Type) [TopologicalSpace X] {n : ℕ}
    (i : Fin (n + 2)) (x : singularSSet X _⦋n + 1⦌) :
    singularSimplexEquiv X n ((singularSSet X).δ i x) =
    SingularChain.face i (singularSimplexEquiv X (n + 1) x) := by
  apply Subtype.ext
  simp only [singularSimplexEquiv, SingularChain.face, stdSimplex.faceMap]
  ; funext t ; rfl

/-- The coefficient group ℤ as an object of `AddCommGrpCat`. -/
def ZGrp : AddCommGrpCat := AddCommGrpCat.of ℤ

variable (X : Type) [TopologicalSpace X]

/-- The comparison map from Mathlib's chain complex to Finsupp-based chains.

Defined using the universal property of the coproduct: each basis element
`ιChainComplex x` maps to `Finsupp.single (e x) 1`. -/
noncomputable def mathlibToFinsupp (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).X n ⟶
    AddCommGrpCat.of (SingularChain ℤ X n) :=
  ((singularSSet X).isColimitChainComplexXCofan ZGrp n).desc
    (Cofan.mk (AddCommGrpCat.of (SingularChain ℤ X n))
      (fun x => AddCommGrpCat.ofHom
        { toFun := fun z : ℤ => z • Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ)
          map_zero' := by simp
          map_add' := by
            intro a b
            simp [add_smul]  }))

/-- The comparison map applied to a basis element. -/
lemma mathlibToFinsupp_ι (n : ℕ) (x : singularSSet X _⦋n⦌) :
    mathlibToFinsupp X n ((singularSSet X).ιChainComplex (R := ZGrp) x (1 : ℤ)) =
    Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ) := by
  let f : (x : singularSSet X _⦋n⦌) → (ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n)) :=
    fun x => AddCommGrpCat.ofHom
      { toFun := fun z : ℤ => z • Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ)
        map_zero' := by simp
        map_add' := by intro a b; simp [add_smul]  }
  let cocone := Cofan.mk (AddCommGrpCat.of (SingularChain ℤ X n)) f
  have h : (singularSSet X).ιChainComplex (R := ZGrp) x ≫ mathlibToFinsupp X n = f x := by
    change (singularSSet X).ιChainComplex (R := ZGrp) x ≫
        ((singularSSet X).isColimitChainComplexXCofan ZGrp n).desc cocone = f x
    exact (singularSSet X).isColimitChainComplexXCofan ZGrp n |>.fac cocone (Discrete.mk x)
  have h2 : (mathlibToFinsupp X n) (((singularSSet X).ιChainComplex (R := ZGrp) x) (1 : ℤ)) =
      (f x) (1 : ℤ) := by
    rw [←h] ; rfl
  have h3 : (f x) (1 : ℤ) = Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ) := by
    dsimp [f, AddCommGrpCat.ofHom]
    ; simp
    ; rfl
  rw [h2, h3]

/-- The forward comparison map from Finsupp-based chains to Mathlib's chain complex,
as an additive map. -/
noncomputable def finsuppToMathlib_addMap (n : ℕ) :
    SingularChain ℤ X n →+ ((singularSSet X).chainComplex ZGrp).X n :=
  let b : SingularSimplex X n → ((singularSSet X).chainComplex ZGrp).X n :=
    fun σ => (singularSSet X).ιChainComplex (R := ZGrp) ((singularSimplexEquiv X n).symm σ) (1 : ℤ)
  let f : SingularSimplex X n → (ℤ →+ ((singularSSet X).chainComplex ZGrp).X n) :=
    fun σ => {
      toFun := fun z : ℤ => z • b σ
      map_zero' := by simp
      map_add' := by intro z1 z2; simp [add_smul]
    }
  Finsupp.liftAddHom f

/-- The forward comparison map as a morphism in `AddCommGrpCat`. -/
noncomputable def finsuppToMathlib (n : ℕ) :
    AddCommGrpCat.of (SingularChain ℤ X n) ⟶
    ((singularSSet X).chainComplex ZGrp).X n :=
  AddCommGrpCat.ofHom (finsuppToMathlib_addMap X n)

/-- The forward comparison map applied to a basis element. -/
lemma finsuppToMathlib_single (n : ℕ) (σ : SingularSimplex X n) :
    (finsuppToMathlib X n).hom (Finsupp.single σ (1 : ℤ)) =
    (singularSSet X).ιChainComplex (R := ZGrp) ((singularSimplexEquiv X n).symm σ) (1 : ℤ) := by
  dsimp only [finsuppToMathlib, finsuppToMathlib_addMap]
  let b : SingularSimplex X n → ((singularSSet X).chainComplex ZGrp).X n :=
    fun τ => (singularSSet X).ιChainComplex (R := ZGrp) ((singularSimplexEquiv X n).symm τ) (1 : ℤ)
  let f : SingularSimplex X n → (ℤ →+ ((singularSSet X).chainComplex ZGrp).X n) :=
    fun τ => {
      toFun := fun z : ℤ => z • b τ
      map_zero' := by simp
      map_add' := by intro z1 z2; simp [add_smul]
    }
  have h_main : (Finsupp.liftAddHom f) (Finsupp.single σ (1 : ℤ)) = b σ := by
    rw [Finsupp.liftAddHom_apply, Finsupp.sum_single_index]
    <;> simp [f, b]
  have h_final : (AddCommGrpCat.ofHom (Finsupp.liftAddHom f)).hom (Finsupp.single σ (1 : ℤ)) = b σ := by
    change (Finsupp.liftAddHom f) (Finsupp.single σ (1 : ℤ)) = b σ
    exact h_main
  exact h_final

/-- The composition additive map: Finsupp → Mathlib → Finsupp. -/
def comp_addMap (n : ℕ) : SingularChain ℤ X n →+ SingularChain ℤ X n :=
  (mathlibToFinsupp X n).hom.comp (finsuppToMathlib X n).hom

/-- The comparison maps are inverse to each other: Finsupp → Mathlib → Finsupp is identity.
Proved by showing the composition agrees with identity on basis elements and using
the universal property of Finsupp. -/
lemma mathlibToFinsupp_leftInverse (n : ℕ) :
    finsuppToMathlib X n ≫ mathlibToFinsupp X n = 𝟙 (AddCommGrpCat.of (SingularChain ℤ X n)) := by
  let g := comp_addMap X n
  have h_main : ∀ (σ : SingularSimplex X n) (z : ℤ),
      g (Finsupp.single σ z) = Finsupp.single σ z := by
    intro σ z
    have h_smul : Finsupp.single σ z = z • Finsupp.single σ (1 : ℤ) := by
      simp
    have h1 : (finsuppToMathlib_addMap X n) (Finsupp.single σ z) =
        z • (finsuppToMathlib_addMap X n) (Finsupp.single σ (1 : ℤ)) := by
      rw [h_smul]
      exact map_zsmul (finsuppToMathlib_addMap X n) z (Finsupp.single σ (1 : ℤ))
    have h1' : (finsuppToMathlib X n).hom (Finsupp.single σ z) =
        z • (singularSSet X).ιChainComplex (R := ZGrp) ((singularSimplexEquiv X n).symm σ) (1 : ℤ) := by
      have h_eq : (finsuppToMathlib X n).hom = finsuppToMathlib_addMap X n := by rfl
      rw [h_eq, h1]
      have h_single : (finsuppToMathlib_addMap X n) (Finsupp.single σ (1 : ℤ)) =
          (singularSSet X).ιChainComplex (R := ZGrp) ((singularSimplexEquiv X n).symm σ) (1 : ℤ) :=
        finsuppToMathlib_single X n σ
      rw [h_single]
    have h3 : g (Finsupp.single σ z) =
        (mathlibToFinsupp X n).hom ((finsuppToMathlib X n).hom (Finsupp.single σ z)) := by
      rfl
    rw [h3, h1']
    have h4 : (mathlibToFinsupp X n).hom (z • (singularSSet X).ιChainComplex (R := ZGrp)
        ((singularSimplexEquiv X n).symm σ) (1 : ℤ)) =
        z • (mathlibToFinsupp X n).hom ((singularSSet X).ιChainComplex (R := ZGrp)
          ((singularSimplexEquiv X n).symm σ) (1 : ℤ)) := by
      simp
    rw [h4, mathlibToFinsupp_ι]
    ; simp
  let b : SingularSimplex X n → (ℤ →+ SingularChain ℤ X n) :=
    fun σ => { toFun := fun z => Finsupp.single σ z
               map_zero' := by simp
               map_add' := by intro z1 z2; simp  }
  have h_g : g = Finsupp.liftAddHom b := by
    have h_symm : Finsupp.liftAddHom.symm g = b := by
      funext σ
      apply AddMonoidHom.ext
      intro z
      have h5 : (Finsupp.liftAddHom (Finsupp.liftAddHom.symm g)) (Finsupp.single σ z) =
          g (Finsupp.single σ z) := by
        rw [Finsupp.liftAddHom.apply_symm_apply]
      have h6 : (Finsupp.liftAddHom (Finsupp.liftAddHom.symm g)) (Finsupp.single σ z) =
          (Finsupp.liftAddHom.symm g) σ z := by
        rw [Finsupp.liftAddHom_apply, Finsupp.sum_single_index]
        ; simp
      rw [h6] at h5
      rw [h5, h_main σ z]
      ; rfl
    have h_eq1 : Finsupp.liftAddHom (Finsupp.liftAddHom.symm g) = Finsupp.liftAddHom b := by
      rw [h_symm]
    have h_eq2 : g = Finsupp.liftAddHom b := by
      simpa [Finsupp.liftAddHom.apply_symm_apply] using h_eq1
    exact h_eq2
  have h_id : (AddMonoidHom.id (SingularChain ℤ X n)) = Finsupp.liftAddHom b := by
    have h_symm : Finsupp.liftAddHom.symm (AddMonoidHom.id (SingularChain ℤ X n)) = b := by
      funext σ
      apply AddMonoidHom.ext
      intro z
      have h5 : (Finsupp.liftAddHom (Finsupp.liftAddHom.symm (AddMonoidHom.id (SingularChain ℤ X n))))
          (Finsupp.single σ z) =
          (AddMonoidHom.id (SingularChain ℤ X n)) (Finsupp.single σ z) := by
        rw [Finsupp.liftAddHom.apply_symm_apply]
      have h6 : (Finsupp.liftAddHom (Finsupp.liftAddHom.symm (AddMonoidHom.id (SingularChain ℤ X n))))
          (Finsupp.single σ z) =
          (Finsupp.liftAddHom.symm (AddMonoidHom.id (SingularChain ℤ X n))) σ z := by
        rw [Finsupp.liftAddHom_apply, Finsupp.sum_single_index]
        ; simp
      rw [h6] at h5
      rw [h5]
      ; rfl
    have h_eq1 : Finsupp.liftAddHom (Finsupp.liftAddHom.symm (AddMonoidHom.id (SingularChain ℤ X n))) =
        Finsupp.liftAddHom b := by
      rw [h_symm]
    have h_eq2 : (AddMonoidHom.id (SingularChain ℤ X n)) = Finsupp.liftAddHom b := by
      simpa [Finsupp.liftAddHom.apply_symm_apply] using h_eq1
    exact h_eq2
  have h_eq : g = AddMonoidHom.id (SingularChain ℤ X n) := by
    rw [h_g, ←h_id]
  apply AddCommGrpCat.ext
  intro c
  simpa [AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply, g, comp_addMap] using
    congr_arg (fun h : SingularChain ℤ X n →+ SingularChain ℤ X n => h c) h_eq

/-- The comparison maps are inverse to each other: Mathlib → Finsupp → Mathlib is identity.
Proved by checking on basis elements using `chainComplex_hom_ext`. -/
lemma mathlibToFinsupp_rightInverse (n : ℕ) :
    mathlibToFinsupp X n ≫ finsuppToMathlib X n = 𝟙 ((singularSSet X).chainComplex ZGrp).X n := by
  apply (singularSSet X).chainComplex_hom_ext (R := ZGrp)
  intro x
  let ι_x : ZGrp ⟶ ((singularSSet X).chainComplex ZGrp).X n :=
    (singularSSet X).ιChainComplex (R := ZGrp) x
  have h_main : ι_x ≫ mathlibToFinsupp X n ≫ finsuppToMathlib X n = ι_x := by
    apply AddCommGrpCat.ext
    intro z
    simp only [AddCommGrpCat.comp_apply]
    let z' : ℤ := z
    have hz : (z : ↑ZGrp) = (z' : ℤ) := by rfl
    have h_i : ι_x.hom z = z' • ι_x.hom (1 : ℤ) := by
      rw [hz]
      have h1 : ∀ (n : ℤ), ι_x.hom (n : ℤ) = n • ι_x.hom (1 : ℤ) := by
        intro n
        have h2 : ι_x.hom (n • (1 : ℤ)) = n • ι_x.hom (1 : ℤ) :=
          ι_x.hom.map_zsmul n (1 : ℤ)
        have h3 : n • (1 : ℤ) = (n : ℤ) := by
          simp
        rw [h3] at h2
        exact h2
      exact h1 z'
    have h1 : (mathlibToFinsupp X n).hom (ι_x.hom z) =
        z' • (mathlibToFinsupp X n).hom (ι_x.hom (1 : ℤ)) := by
      rw [h_i]
      exact (mathlibToFinsupp X n).hom.map_zsmul z' (ι_x.hom (1 : ℤ))
    have h2 : (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom (ι_x.hom z)) =
        z' • (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom (ι_x.hom (1 : ℤ))) := by
      rw [h1]
      exact (finsuppToMathlib X n).hom.map_zsmul z'
        ((mathlibToFinsupp X n).hom (ι_x.hom (1 : ℤ)))
    rw [h2]
    have h3 : (mathlibToFinsupp X n).hom (ι_x.hom (1 : ℤ)) =
        Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ) :=
      mathlibToFinsupp_ι X n x
    rw [h3]
    have h4 : (finsuppToMathlib X n).hom (Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ)) =
        (singularSSet X).ιChainComplex (R := ZGrp)
          ((singularSimplexEquiv X n).symm (singularSimplexEquiv X n x)) (1 : ℤ) :=
      finsuppToMathlib_single X n (singularSimplexEquiv X n x)
    rw [h4]
    have h5 : (singularSimplexEquiv X n).symm (singularSimplexEquiv X n x) = x := by simp
    rw [h5]
    have h6 : z' • ι_x.hom (1 : ℤ) = ι_x.hom z := by
      rw [hz]
      have h1 : ∀ (n : ℤ), n • ι_x.hom (1 : ℤ) = ι_x.hom (n : ℤ) := by
        intro n
        have h2 : n • ι_x.hom (1 : ℤ) = ι_x.hom (n • (1 : ℤ)) :=
          (ι_x.hom.map_zsmul n (1 : ℤ)).symm
        have h3 : n • (1 : ℤ) = (n : ℤ) := by simp
        rw [h3] at h2
        exact h2
      exact h1 z'
    rw [h6]
  simpa [ι_x] using h_main

/-- The boundary map on Finsupp chains as an `AddMonoidHom`. -/
def d_addMap (n : ℕ) : SingularChain ℤ X (n + 1) →+ SingularChain ℤ X n :=
  { toFun := SingularChain.d n
    map_zero' := by simp [SingularChain.d]
    map_add' := SingularChain.d_add n }

/-- The boundary map on Finsupp chains as a morphism in `AddCommGrpCat`. -/
def d_morphism (n : ℕ) :
    AddCommGrpCat.of (SingularChain ℤ X (n + 1)) ⟶ AddCommGrpCat.of (SingularChain ℤ X n) :=
  AddCommGrpCat.ofHom (d_addMap X n)

/-- The formula for the Finsupp boundary on a single simplex. -/
lemma d_single (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    SingularChain.d n (Finsupp.single σ (1 : ℤ)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (SingularChain.face i σ) (1 : ℤ) := by
  dsimp only [SingularChain.d]
  rw [Finsupp.sum_single_index (by simp)] ; simp [one_smul]

/-- `mathlibToFinsupp` commutes with the boundary map (it is a chain map). -/
lemma mathlibToFinsupp_chainMap (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n =
    mathlibToFinsupp X (n + 1) ≫ d_morphism X n := by
  apply (singularSSet X).chainComplex_hom_ext (R := ZGrp)
  intro x
  let ι_x : ZGrp ⟶ ((singularSSet X).chainComplex ZGrp).X (n + 1) :=
    (singularSSet X).ιChainComplex (R := ZGrp) x
  let lhs : ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n) :=
    ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n
  let rhs : ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n) :=
    ι_x ≫ mathlibToFinsupp X (n + 1) ≫ d_morphism X n
  have h_lhs1 : ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x)) ≫
      mathlibToFinsupp X n := by
    have h_step1 : ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) :=
      (singularSSet X).ιChainComplex_d (R := ZGrp) x
    exact congr_arg (fun f : ZGrp ⟶ ((singularSSet X).chainComplex ZGrp).X n =>
      f ≫ mathlibToFinsupp X n) h_step1
  have h_lhs2 : ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) ≫
          mathlibToFinsupp X n) := by
    rw [h_lhs1]
    rw [Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    exact Preadditive.zsmul_comp
      ((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x))
      (mathlibToFinsupp X n) ((-1 : ℤ) ^ (i : ℕ))
  have h_rhs1 : (ι_x ≫ mathlibToFinsupp X (n + 1) ≫ d_morphism X n).hom (1 : ℤ) =
      (d_morphism X n).hom
        ((mathlibToFinsupp X (n + 1)).hom (ι_x.hom (1 : ℤ))) := by
    dsimp only [ι_x]
    ; rfl
  have h_core : (ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n).hom (1 : ℤ) =
      (ι_x ≫ mathlibToFinsupp X (n + 1) ≫ d_morphism X n).hom (1 : ℤ) := by
    have h_sum_hom : ∀ (s : Finset (Fin (n + 2)))
        (g : Fin (n + 2) → (ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n))),
        (∑ i ∈ s, g i).hom (1 : ℤ) = ∑ i ∈ s, (g i).hom (1 : ℤ) := by
      intro s g
      induction s using Finset.induction with
      | empty =>
        simp
      | @insert a s ha ih =>
        calc
          (∑ i ∈ insert a s, g i).hom (1 : ℤ)
            = (g a + ∑ i ∈ s, g i).hom (1 : ℤ) := by rw [Finset.sum_insert ha]
          _ = (g a).hom (1 : ℤ) + (∑ i ∈ s, g i).hom (1 : ℤ) := by
            exact Finsupp.ext (congrFun rfl)
          _ = (g a).hom (1 : ℤ) + ∑ i ∈ s, (g i).hom (1 : ℤ) := by rw [ih]
          _ = ∑ i ∈ insert a s, (g i).hom (1 : ℤ) := by
            rw [Finset.sum_insert ha]
    let f (i : Fin (n + 2)) : ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n) :=
      (-1 : ℤ) ^ (i : ℕ) •
        ((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) ≫
          mathlibToFinsupp X n)
    have h_sum_lhs1 : (ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n) =
        ∑ i : Fin (n + 2), f i := h_lhs2
    have h_sum_lhs2 : (∑ i : Fin (n + 2), f i).hom (1 : ℤ) =
        ∑ i : Fin (n + 2), (f i).hom (1 : ℤ) := h_sum_hom Finset.univ f
    have h_final : ∀ (i : Fin (n + 2)), (f i).hom (1 : ℤ) =
        (-1 : ℤ) ^ (i : ℕ) •
          (mathlibToFinsupp X n).hom
            ((singularSSet X).ιChainComplex (R := ZGrp)
              ((singularSSet X).δ i x) (1 : ℤ)) := by
      intro i
      dsimp only [f]
      have h_zsmul : ((-1 : ℤ) ^ (i : ℕ) •
          ((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) ≫
            mathlibToFinsupp X n)).hom (1 : ℤ) =
          (-1 : ℤ) ^ (i : ℕ) •
            (((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) ≫
              mathlibToFinsupp X n).hom (1 : ℤ)) := by exact Finsupp.ext (congrFun rfl)
      have h_comp : (((singularSSet X).ιChainComplex (R := ZGrp) ((singularSSet X).δ i x) ≫
          mathlibToFinsupp X n).hom (1 : ℤ)) =
          (mathlibToFinsupp X n).hom
            ((singularSSet X).ιChainComplex (R := ZGrp)
              ((singularSSet X).δ i x) (1 : ℤ)) := by
        dsimp only [AddCommGrpCat.comp_apply]
        ; rfl
      rw [h_zsmul, h_comp]
    have h_sum_lhs : (ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n).hom (1 : ℤ) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (mathlibToFinsupp X n).hom
            ((singularSSet X).ιChainComplex (R := ZGrp)
              ((singularSSet X).δ i x) (1 : ℤ)) := by
      calc
        (ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n).hom (1 : ℤ)
          = (∑ i : Fin (n + 2), f i).hom (1 : ℤ) := by rw [h_sum_lhs1]
        _ = ∑ i : Fin (n + 2), (f i).hom (1 : ℤ) := h_sum_lhs2
        _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
              (mathlibToFinsupp X n).hom
                ((singularSSet X).ιChainComplex (R := ZGrp)
                  ((singularSSet X).δ i x) (1 : ℤ)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_final i
    rw [h_sum_lhs, h_rhs1]
    have h_ι : (mathlibToFinsupp X (n + 1)).hom (ι_x.hom (1 : ℤ)) =
        Finsupp.single (singularSimplexEquiv X (n + 1) x) (1 : ℤ) := by
      exact mathlibToFinsupp_ι X (n + 1) x
    rw [h_ι]
    have h_dsingle : (d_morphism X n).hom
        (Finsupp.single (singularSimplexEquiv X (n + 1) x) (1 : ℤ)) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          Finsupp.single
            (SingularChain.face i (singularSimplexEquiv X (n + 1) x)) (1 : ℤ) := by
      simpa [d_morphism, d_addMap] using d_single X n (singularSimplexEquiv X (n + 1) x)
    rw [h_dsingle]
    apply Finset.sum_congr rfl
    intro i _
    have h_ι2 : (mathlibToFinsupp X n).hom
        ((singularSSet X).ιChainComplex (R := ZGrp)
          ((singularSSet X).δ i x) (1 : ℤ)) =
        Finsupp.single (singularSimplexEquiv X n ((singularSSet X).δ i x)) (1 : ℤ) :=
      mathlibToFinsupp_ι X n ((singularSSet X).δ i x)
    rw [h_ι2, singularSimplexEquiv_face X i x]
  have h_eq : ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n =
      ι_x ≫ mathlibToFinsupp X (n + 1) ≫ d_morphism X n := by
    apply AddCommGrpCat.ext
    intro z
    let z' : ℤ := z
    have hz : (z : ↑ZGrp) = (z' : ℤ) := by rfl
    have h1 : ∀ (f : ZGrp ⟶ AddCommGrpCat.of (SingularChain ℤ X n)),
        f.hom z = z' • f.hom (1 : ℤ) := by
      intro f
      rw [hz]
      have h2 : f.hom (z' • (1 : ℤ)) = z' • f.hom (1 : ℤ) :=
        f.hom.map_zsmul z' (1 : ℤ)
      have h3 : z' • (1 : ℤ) = (z' : ℤ) := by simp
      rw [h3] at h2
      exact h2
    rw [h1 (ι_x ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n),
        h1 (ι_x ≫ mathlibToFinsupp X (n + 1) ≫ d_morphism X n), h_core]
  simpa [ι_x] using h_eq

/-- `finsuppToMathlib` also commutes with the boundary map.
Follows from `mathlibToFinsupp_chainMap` and the isomorphism. -/
lemma finsuppToMathlib_chainMap (n : ℕ) :
    d_morphism X n ≫ finsuppToMathlib X n =
    finsuppToMathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n := by
  calc
    d_morphism X n ≫ finsuppToMathlib X n
      = (finsuppToMathlib X (n + 1) ≫ mathlibToFinsupp X (n + 1)) ≫
          d_morphism X n ≫ finsuppToMathlib X n := by
        rw [mathlibToFinsupp_leftInverse X (n + 1)]
        ; simp
    _ = finsuppToMathlib X (n + 1) ≫
          (mathlibToFinsupp X (n + 1) ≫ d_morphism X n) ≫ finsuppToMathlib X n := by
        simp [Category.assoc]
    _ = finsuppToMathlib X (n + 1) ≫
          (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n) ≫
          finsuppToMathlib X n := by
        rw [mathlibToFinsupp_chainMap X n]
    _ = finsuppToMathlib X (n + 1) ≫
          ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
          (mathlibToFinsupp X n ≫ finsuppToMathlib X n) := by
        simp [Category.assoc]
    _ = finsuppToMathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n := by
        rw [mathlibToFinsupp_rightInverse X n]
        ; simp [Category.comp_id]

/-- Barycentric subdivision on Mathlib's singular chains, defined by transport. -/
noncomputable def sd_mathlib (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).X n ⟶ ((singularSSet X).chainComplex ZGrp).X n :=
  mathlibToFinsupp X n ≫
    AddCommGrpCat.ofHom
      { toFun := sdMap n
        map_zero' := by simp [sdMap]
        map_add' := sdMap_add n } ≫
    finsuppToMathlib X n

/-- Barycentric subdivision on Mathlib's chains is a chain map. -/
lemma sd_mathlib_chainMap (n : ℕ) :
    sd_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n =
    ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ sd_mathlib X n := by
  dsimp only [sd_mathlib]
  calc
    (mathlibToFinsupp X (n + 1) ≫ AddCommGrpCat.ofHom
        { toFun := sdMap (n + 1)
          map_zero' := by simp [sdMap]
          map_add' := sdMap_add (n + 1) } ≫
        finsuppToMathlib X (n + 1)) ≫
      ((singularSSet X).chainComplex ZGrp).d (n + 1) n
      = mathlibToFinsupp X (n + 1) ≫ AddCommGrpCat.ofHom
          { toFun := sdMap (n + 1)
            map_zero' := by simp [sdMap]
            map_add' := sdMap_add (n + 1) } ≫
          (finsuppToMathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n) := by
        simp [Category.assoc]
    _ = mathlibToFinsupp X (n + 1) ≫ AddCommGrpCat.ofHom
          { toFun := sdMap (n + 1)
            map_zero' := by simp [sdMap]
            map_add' := sdMap_add (n + 1) } ≫
          (d_morphism X n ≫ finsuppToMathlib X n) := by
        rw [finsuppToMathlib_chainMap X n]
    _ = mathlibToFinsupp X (n + 1) ≫
          (AddCommGrpCat.ofHom
            { toFun := sdMap (n + 1)
              map_zero' := by simp [sdMap]
              map_add' := sdMap_add (n + 1) } ≫
            d_morphism X n) ≫ finsuppToMathlib X n := by
        simp [Category.assoc]
    _ = mathlibToFinsupp X (n + 1) ≫
          (d_morphism X n ≫ AddCommGrpCat.ofHom
            { toFun := sdMap n
              map_zero' := by simp [sdMap]
              map_add' := sdMap_add n }) ≫
          finsuppToMathlib X n := by
        congr 1
        apply AddCommGrpCat.ext
        intro c
        have h : SingularChain.d n (sdMap (n + 1) c) = sdMap n (SingularChain.d n c) :=
          sd_chainMap n c
        exact congr_arg (finsuppToMathlib X n).hom h
    _ = (mathlibToFinsupp X (n + 1) ≫ d_morphism X n) ≫
          AddCommGrpCat.ofHom
            { toFun := sdMap n
              map_zero' := by simp [sdMap]
              map_add' := sdMap_add n } ≫
          finsuppToMathlib X n := by
        simp [Category.assoc]
    _ = (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n) ≫
          AddCommGrpCat.ofHom
            { toFun := sdMap n
              map_zero' := by simp [sdMap]
              map_add' := sdMap_add n } ≫
          finsuppToMathlib X n := by
        rw [mathlibToFinsupp_chainMap X n]
    _ = ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
          (mathlibToFinsupp X n ≫ AddCommGrpCat.ofHom
            { toFun := sdMap n
              map_zero' := by simp [sdMap]
              map_add' := sdMap_add n } ≫
            finsuppToMathlib X n) := by
        simp [Category.assoc]

/-- The chain homotopy operator T on Mathlib's singular chains, defined by transport. -/
noncomputable def T_mathlib (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).X n ⟶ ((singularSSet X).chainComplex ZGrp).X (n + 1) :=
  mathlibToFinsupp X n ≫
    AddCommGrpCat.ofHom
      { toFun := TMap n
        map_zero' := by simp [TMap]
        map_add' := TMap_add n } ≫
    finsuppToMathlib X (n + 1)

/-- Helper: applying a sum of morphisms equals sum of applications. -/
lemma hom_add_apply {A B : AddCommGrpCat} (f g : A ⟶ B) (x : A) :
    (f + g).hom x = f.hom x + g.hom x := by
  exact AddCommGrpCat.hom_add_apply f g x

/-- Helper: applying a negated morphism equals negation of application. -/
lemma hom_neg_apply {A B : AddCommGrpCat} (f : A ⟶ B) (x : A) :
    (-f).hom x = - (f.hom x) := by
  have h1 : f + (-f) = (0 : A ⟶ B) := by
    exact add_neg_cancel f
  have h2 : (f + (-f)).hom x = (0 : A ⟶ B).hom x := by rw [h1]
  have h3 : (f + (-f)).hom x = f.hom x + (-f).hom x := hom_add_apply f (-f) x
  have h4 : (0 : A ⟶ B).hom x = 0 := by simp
  have h5 : f.hom x + (-f).hom x = 0 := by
    rw [←h3, h2, h4]
  have h6 : (-f).hom x = - (f.hom x) := by
    have h7 : f.hom x + (-f).hom x = 0 := h5
    have h8 : (-f).hom x = - (f.hom x) := by
      calc
        (-f).hom x = f.hom x + (-f).hom x + (- (f.hom x)) := by abel
        _ = 0 + (- (f.hom x)) := by rw [h7]
        _ = - (f.hom x) := by abel
    exact h8
  exact h6

/-- Helper: applying a difference of morphisms equals difference of applications. -/
lemma hom_sub_apply {A B : AddCommGrpCat} (f g : A ⟶ B) (x : A) :
    (f - g).hom x = f.hom x - g.hom x := by
  have h1 : f - g = f + (-g) := by exact SubNegMonoid.sub_eq_add_neg f g
  have h2 : (f - g).hom x = (f + (-g)).hom x := by rw [h1]
  rw [h2, hom_add_apply f (-g) x, hom_neg_apply g x]
  ; abel

/-- The chain homotopy equation on Mathlib's chains:
`T ∘ d + d ∘ T = sd - id`. Both sides are endomorphisms of degree n+1 chains. -/
theorem sd_mathlib_homotopy (n : ℕ) :
    T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1) +
    ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n =
    sd_mathlib X (n + 1) - 𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1) := by
  apply AddCommGrpCat.ext
  intro x
  let c := (mathlibToFinsupp X (n + 1)).hom x
  have hx : x = (finsuppToMathlib X (n + 1)).hom c := by
    have h_rightInv : (mathlibToFinsupp X (n + 1) ≫ finsuppToMathlib X (n + 1)).hom x =
        (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x := by
      rw [mathlibToFinsupp_rightInverse X (n + 1)]
    have h_comp : (mathlibToFinsupp X (n + 1) ≫ finsuppToMathlib X (n + 1)).hom x =
        (finsuppToMathlib X (n + 1)).hom c := by
      simp [c]
    have h_id : (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x = x := by
      simp
    have h4 : (finsuppToMathlib X (n + 1)).hom c =
        (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x := by
      exact h_comp.symm.trans h_rightInv
    have h5 : (finsuppToMathlib X (n + 1)).hom c = x := by
      rw [h_id] at h4
      exact h4
    exact h5.symm
  have h1 : (T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom x =
      (finsuppToMathlib X (n + 1)).hom
        (SingularChain.d (n + 1) (TMap (n + 1) c)) := by
    dsimp only [T_mathlib]
    have h_comp : (mathlibToFinsupp X (n + 1) ≫
        AddCommGrpCat.ofHom
          { toFun := TMap (n + 1)
            map_zero' := by simp [TMap]
            map_add' := TMap_add (n + 1) } ≫
        finsuppToMathlib X (n + 2) ≫
        ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom x =
        (finsuppToMathlib X (n + 1)).hom
          (SingularChain.d (n + 1) (TMap (n + 1) c)) := by
      have h_ψ : finsuppToMathlib X (n + 2) ≫
          ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1) =
          d_morphism X (n + 1) ≫ finsuppToMathlib X (n + 1) :=
        (finsuppToMathlib_chainMap X (n + 1)).symm
      calc
        (mathlibToFinsupp X (n + 1) ≫
            AddCommGrpCat.ofHom
              { toFun := TMap (n + 1)
                map_zero' := by simp [TMap]
                map_add' := TMap_add (n + 1) } ≫
            finsuppToMathlib X (n + 2) ≫
            ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom x
          = (mathlibToFinsupp X (n + 1) ≫
              AddCommGrpCat.ofHom
                { toFun := TMap (n + 1)
                  map_zero' := by simp [TMap]
                  map_add' := TMap_add (n + 1) } ≫
              d_morphism X (n + 1) ≫ finsuppToMathlib X (n + 1)).hom x := by
            rw [h_ψ]
        _ = (finsuppToMathlib X (n + 1)).hom
              ((d_morphism X (n + 1)).hom
                ((AddCommGrpCat.ofHom
                  { toFun := TMap (n + 1)
                    map_zero' := by simp [TMap]
                    map_add' := TMap_add (n + 1) }).hom
                  ((mathlibToFinsupp X (n + 1)).hom x))) := by
            simp
        _ = (finsuppToMathlib X (n + 1)).hom
              (SingularChain.d (n + 1) (TMap (n + 1) c)) := by
            dsimp only [c, d_morphism, d_addMap] ; rfl
    simpa [AddCommGrpCat.comp_apply] using h_comp
  have h2 : (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n).hom x =
      (finsuppToMathlib X (n + 1)).hom
        (TMap n (SingularChain.d n c)) := by
    dsimp only [T_mathlib]
    have h_chainMap : ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
        mathlibToFinsupp X n =
        mathlibToFinsupp X (n + 1) ≫ d_morphism X n :=
      mathlibToFinsupp_chainMap X n
    have h_morph : ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
        mathlibToFinsupp X n ≫
        AddCommGrpCat.ofHom
          { toFun := TMap n
            map_zero' := by simp [TMap]
            map_add' := TMap_add n } ≫
        finsuppToMathlib X (n + 1) =
        mathlibToFinsupp X (n + 1) ≫ d_morphism X n ≫
        AddCommGrpCat.ofHom
          { toFun := TMap n
            map_zero' := by simp [TMap]
            map_add' := TMap_add n } ≫
        finsuppToMathlib X (n + 1) := by
      calc
        ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
            mathlibToFinsupp X n ≫
            AddCommGrpCat.ofHom
              { toFun := TMap n
                map_zero' := by simp [TMap]
                map_add' := TMap_add n } ≫
            finsuppToMathlib X (n + 1)
          = ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
              (mathlibToFinsupp X n ≫
                AddCommGrpCat.ofHom
                  { toFun := TMap n
                    map_zero' := by simp [TMap]
                    map_add' := TMap_add n }) ≫
              finsuppToMathlib X (n + 1) := by
            simp [Category.assoc]
        _ = (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
              mathlibToFinsupp X n) ≫
            AddCommGrpCat.ofHom
              { toFun := TMap n
                map_zero' := by simp [TMap]
                map_add' := TMap_add n } ≫
            finsuppToMathlib X (n + 1) := by
            simp [Category.assoc]
        _ = (mathlibToFinsupp X (n + 1) ≫ d_morphism X n) ≫
            AddCommGrpCat.ofHom
              { toFun := TMap n
                map_zero' := by simp [TMap]
                map_add' := TMap_add n } ≫
            finsuppToMathlib X (n + 1) := by
            rw [h_chainMap]
        _ = mathlibToFinsupp X (n + 1) ≫
            d_morphism X n ≫
            AddCommGrpCat.ofHom
              { toFun := TMap n
                map_zero' := by simp [TMap]
                map_add' := TMap_add n } ≫
            finsuppToMathlib X (n + 1) := by
            simp [Category.assoc]
    have h_comp : (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫
        mathlibToFinsupp X n ≫
        AddCommGrpCat.ofHom
          { toFun := TMap n
            map_zero' := by simp [TMap]
            map_add' := TMap_add n } ≫
        finsuppToMathlib X (n + 1)).hom x =
        (finsuppToMathlib X (n + 1)).hom (TMap n (SingularChain.d n c)) := by
      rw [h_morph]
      simp [c, d_morphism, d_addMap]
    simpa [AddCommGrpCat.comp_apply] using h_comp
  have h3 : (sd_mathlib X (n + 1) - 𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x =
      (finsuppToMathlib X (n + 1)).hom (sdMap (n + 1) c - c) := by
    have h_sub : (sd_mathlib X (n + 1) - 𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x =
        (sd_mathlib X (n + 1)).hom x - (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x :=
      hom_sub_apply (sd_mathlib X (n + 1)) (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)) x
    have h_sd : (sd_mathlib X (n + 1)).hom x =
        (finsuppToMathlib X (n + 1)).hom (sdMap (n + 1) c) := by
      dsimp only [sd_mathlib, c]
      simp
    have h_id : (𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x = x := by
      simp
    rw [h_sub, h_sd, h_id, hx]
    have h_map_sub : (finsuppToMathlib X (n + 1)).hom (sdMap (n + 1) c) -
        (finsuppToMathlib X (n + 1)).hom c =
        (finsuppToMathlib X (n + 1)).hom (sdMap (n + 1) c - c) := by
      rw [←map_sub]
    exact h_map_sub
  have h_main : (T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1) +
      ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n).hom x =
      (sd_mathlib X (n + 1) - 𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1)).hom x := by
    have h_add : (T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1) +
        ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n).hom x =
        (T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom x +
        (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n).hom x :=
      hom_add_apply
        (T_mathlib X (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1))
        (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib X n)
        x
    have h_chainHomotopy : SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c) =
        sdMap (n + 1) c - c := chainHomotopy n c
    have h_add2 : (finsuppToMathlib X (n + 1)).hom
        (SingularChain.d (n + 1) (TMap (n + 1) c)) +
        (finsuppToMathlib X (n + 1)).hom (TMap n (SingularChain.d n c)) =
        (finsuppToMathlib X (n + 1)).hom
          (SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c)) := by
      rw [←map_add]
    have h_final : (finsuppToMathlib X (n + 1)).hom
        (SingularChain.d (n + 1) (TMap (n + 1) c) + TMap n (SingularChain.d n c)) =
        (finsuppToMathlib X (n + 1)).hom (sdMap (n + 1) c - c) := by
      rw [h_chainHomotopy]
    rw [h_add, h1, h2, h_add2, h_final, h3]
  exact h_main

/-- Iterated barycentric subdivision: sd^k on Mathlib's chains. -/
noncomputable def sd_mathlib_iter (k : ℕ) (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).X n ⟶ ((singularSSet X).chainComplex ZGrp).X n :=
  Nat.recOn k (𝟙 _) fun _ ih => ih ≫ sd_mathlib X n

/-- Iterated sd is a chain map: sd^k ∘ d = d ∘ sd^k. -/
lemma sd_mathlib_iter_chainMap (k : ℕ) (n : ℕ) :
    sd_mathlib_iter X k (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 1) n =
    ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ sd_mathlib_iter X k n := by
  let d_n := ((singularSSet X).chainComplex ZGrp).d (n + 1) n
  induction k with
  | zero =>
    dsimp only [sd_mathlib_iter]
    ; simp
  | succ k ih =>
    dsimp only [sd_mathlib_iter]
    let sd_k_n1 := sd_mathlib_iter X k (n + 1)
    let sd_k_n := sd_mathlib_iter X k n
    have h : (sd_k_n1 ≫ sd_mathlib X (n + 1)) ≫ d_n = d_n ≫ (sd_k_n ≫ sd_mathlib X n) := by
      calc
        (sd_k_n1 ≫ sd_mathlib X (n + 1)) ≫ d_n
          = sd_k_n1 ≫ (sd_mathlib X (n + 1) ≫ d_n) :=
            Category.assoc sd_k_n1 (sd_mathlib X (n + 1)) d_n
        _ = sd_k_n1 ≫ (d_n ≫ sd_mathlib X n) := by
            rw [sd_mathlib_chainMap X n]
        _ = (sd_k_n1 ≫ d_n) ≫ sd_mathlib X n :=
            (Category.assoc sd_k_n1 d_n (sd_mathlib X n)).symm
        _ = (d_n ≫ sd_k_n) ≫ sd_mathlib X n := by rw [ih]
        _ = d_n ≫ (sd_k_n ≫ sd_mathlib X n) :=
            Category.assoc d_n sd_k_n (sd_mathlib X n)
    exact h

/-- Iterated chain homotopy T_k = Σ_{i=0}^{k-1} T ∘ sd^i on Mathlib's chains. -/
noncomputable def T_mathlib_iter (k : ℕ) (n : ℕ) :
    ((singularSSet X).chainComplex ZGrp).X n ⟶ ((singularSSet X).chainComplex ZGrp).X (n + 1) :=
  Nat.recOn k (0 : _) fun k ih => ih + sd_mathlib_iter X k n ≫ T_mathlib X n

/-- Iterated chain homotopy formula: d(T_k(c)) + T_k(d(c)) = sd^k(c) - c. -/
theorem sd_mathlib_iter_homotopy (k : ℕ) (n : ℕ) :
    T_mathlib_iter X k (n + 1) ≫ ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1) +
    ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ T_mathlib_iter X k n =
    sd_mathlib_iter X k (n + 1) - 𝟙 ((singularSSet X).chainComplex ZGrp).X (n + 1) := by
  let d1 := ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)
  let d0 := ((singularSSet X).chainComplex ZGrp).d (n + 1) n
  induction k with
  | zero =>
    dsimp only [T_mathlib_iter, sd_mathlib_iter]
    ; simp
  | succ k ih =>
    dsimp only [T_mathlib_iter, sd_mathlib_iter]
    let T_k_n1 := T_mathlib_iter X k (n + 1)
    let T_k_n := T_mathlib_iter X k n
    let sd_k_n1 := sd_mathlib_iter X k (n + 1)
    let sd_k_n := sd_mathlib_iter X k n
    have h_main : (T_k_n1 + sd_k_n1 ≫ T_mathlib X (n + 1)) ≫ d1 +
        d0 ≫ (T_k_n + sd_k_n ≫ T_mathlib X n) =
        (sd_k_n1 ≫ sd_mathlib X (n + 1)) - 𝟙 _ := by
      have h1 : (T_k_n1 + sd_k_n1 ≫ T_mathlib X (n + 1)) ≫ d1 =
          T_k_n1 ≫ d1 + sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1) := by
        rw [Preadditive.add_comp]
        ; rw [Category.assoc]
      have h2 : d0 ≫ (T_k_n + sd_k_n ≫ T_mathlib X n) =
          d0 ≫ T_k_n + sd_k_n1 ≫ (d0 ≫ T_mathlib X n) := by
        have h_comm : d0 ≫ sd_k_n = sd_k_n1 ≫ d0 := (sd_mathlib_iter_chainMap X k n).symm
        calc
          d0 ≫ (T_k_n + sd_k_n ≫ T_mathlib X n)
            = d0 ≫ T_k_n + d0 ≫ (sd_k_n ≫ T_mathlib X n) := by
              rw [Preadditive.comp_add]
          _ = d0 ≫ T_k_n + (d0 ≫ sd_k_n) ≫ T_mathlib X n := by
              rw [Category.assoc d0 sd_k_n (T_mathlib X n)]
          _ = d0 ≫ T_k_n + (sd_k_n1 ≫ d0) ≫ T_mathlib X n := by rw [h_comm]
          _ = d0 ≫ T_k_n + sd_k_n1 ≫ (d0 ≫ T_mathlib X n) := by
              rw [Category.assoc sd_k_n1 d0 (T_mathlib X n)]
      have h3 : (T_k_n1 + sd_k_n1 ≫ T_mathlib X (n + 1)) ≫ d1 +
          d0 ≫ (T_k_n + sd_k_n ≫ T_mathlib X n) =
          (T_k_n1 ≫ d1 + d0 ≫ T_k_n) +
          sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1 + d0 ≫ T_mathlib X n) := by
        rw [h1, h2]
        have h_abel : T_k_n1 ≫ d1 + sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1) +
            (d0 ≫ T_k_n + sd_k_n1 ≫ (d0 ≫ T_mathlib X n)) =
            (T_k_n1 ≫ d1 + d0 ≫ T_k_n) +
            (sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1) + sd_k_n1 ≫ (d0 ≫ T_mathlib X n)) := by
          abel
        rw [h_abel]
        have h_comp_add : sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1) + sd_k_n1 ≫ (d0 ≫ T_mathlib X n) =
            sd_k_n1 ≫ (T_mathlib X (n + 1) ≫ d1 + d0 ≫ T_mathlib X n) := by
          rw [←Preadditive.comp_add]
        rw [h_comp_add]
      rw [h3]
      have h4 : T_k_n1 ≫ d1 + d0 ≫ T_k_n = sd_k_n1 - 𝟙 _ := ih
      have h5 : T_mathlib X (n + 1) ≫ d1 + d0 ≫ T_mathlib X n =
          sd_mathlib X (n + 1) - 𝟙 _ := sd_mathlib_homotopy X n
      rw [h4, h5]
      ; simp
    exact h_main

/-!
### Small chain theorem: algebraic core

Given that iterated barycentric subdivision eventually makes chains small,
the inclusion of small chains into all chains induces isomorphisms on homology.

We prove the two key algebraic facts:
1. Surjectivity: every cycle is homologous to an sd^k-cycle
2. Injectivity: if a cycle bounds, it bounds via sd^k + T_k

The geometric facts (sd preserves small, T preserves small, sd^k eventually small)
are assumed as hypotheses.
-/

/-- If z is a cycle (d(z) = 0), then sd^k(z) - z is a boundary:
`sd^k(z) - z = d(T_k(z))`.
Hence z and sd^k(z) are homologous. -/
lemma sd_iter_homotopy_on_cycles (k : ℕ) (n : ℕ)
    (z : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hz : (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom z = 0) :
    (sd_mathlib_iter X k (n + 1)).hom z - z =
    (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom
      ((T_mathlib_iter X k (n + 1)).hom z) := by
  let d1 := ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)
  let d0 := ((singularSSet X).chainComplex ZGrp).d (n + 1) n
  let T_k1 := T_mathlib_iter X k (n + 1)
  let T_k0 := T_mathlib_iter X k n
  let sd_k1 := sd_mathlib_iter X k (n + 1)
  have h_hom : T_k1 ≫ d1 + d0 ≫ T_k0 = sd_k1 - 𝟙 _ :=
    sd_mathlib_iter_homotopy X k n
  have h2 : (T_k1 ≫ d1 + d0 ≫ T_k0).hom z = (sd_k1 - 𝟙 _).hom z := by
    rw [h_hom]
  have h3 : (T_k1 ≫ d1 + d0 ≫ T_k0).hom z =
      (T_k1 ≫ d1).hom z + (d0 ≫ T_k0).hom z :=
    hom_add_apply (T_k1 ≫ d1) (d0 ≫ T_k0) z
  have h4 : (T_k1 ≫ d1).hom z = d1.hom (T_k1.hom z) := by
    simp
  have h5 : (d0 ≫ T_k0).hom z = T_k0.hom (d0.hom z) := by
    simp
  have h6 : (sd_k1 - 𝟙 _).hom z = sd_k1.hom z - z := by
    rw [hom_sub_apply]
    ; simp
  rw [h3, h4, h5, hz] at h2
  ; simp at h2
  ; exact h2.symm

/-- If z = d(b), then z = d(sd^k(b) - T_k(z)).
Hence if sd^k(b) and T_k(z) are small, then z is a small boundary. -/
lemma sd_iter_boundary_decomposition (k : ℕ) (n : ℕ)
    (b : ((singularSSet X).chainComplex ZGrp).X (n + 2))
    (z : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hz : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom b = z) :
    z = (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom
      ((sd_mathlib_iter X k (n + 2)).hom b - (T_mathlib_iter X k (n + 1)).hom z) := by
  let d2 := ((singularSSet X).chainComplex ZGrp).d (n + 3) (n + 2)
  let d1 := ((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)
  let d0 := ((singularSSet X).chainComplex ZGrp).d (n + 1) n
  let T_k2 := T_mathlib_iter X k (n + 2)
  let T_k1 := T_mathlib_iter X k (n + 1)
  let T_k0 := T_mathlib_iter X k n
  let sd_k2 := sd_mathlib_iter X k (n + 2)
  let sd_k1 := sd_mathlib_iter X k (n + 1)
  -- z is a cycle (since z = d(b) and d^2 = 0)
  have h_z_cycle : d0.hom z = 0 := by
    have h_d2 : d1 ≫ d0 = 0 := by exact ((singularSSet X).chainComplex ZGrp).d_comp_d' (n + 2) (n + 1) n rfl rfl
    have h : d0.hom (d1.hom b) = 0 := by
      have h2 : (d1 ≫ d0).hom b = 0 := by rw [h_d2] ; simp
      simpa [AddCommGrpCat.comp_apply] using h2
    rw [hz] at *
    ; exact h
  -- Homotopy formula at degree n+1: d(T_k(z)) + T_k(d(z)) = sd^k(z) - z
  have h_hom1 : T_k1 ≫ d1 + d0 ≫ T_k0 = sd_k1 - 𝟙 _ :=
    sd_mathlib_iter_homotopy X k n
  have h_apply1 : (T_k1 ≫ d1 + d0 ≫ T_k0).hom z = (sd_k1 - 𝟙 _).hom z := by
    rw [h_hom1]
  have h_eq1 : d1.hom (T_k1.hom z) + T_k0.hom (d0.hom z) = sd_k1.hom z - z := by
    have h1 : (T_k1 ≫ d1 + d0 ≫ T_k0).hom z =
        (T_k1 ≫ d1).hom z + (d0 ≫ T_k0).hom z := hom_add_apply (T_k1 ≫ d1) (d0 ≫ T_k0) z
    have h2 : (T_k1 ≫ d1).hom z = d1.hom (T_k1.hom z) := by
      simp
    have h3 : (d0 ≫ T_k0).hom z = T_k0.hom (d0.hom z) := by
      simp
    have h4 : (sd_k1 - 𝟙 _).hom z = sd_k1.hom z - z := by
      rw [hom_sub_apply] ; simp
    rw [h1, h2, h3, h4] at h_apply1
    exact h_apply1
  -- Since d(z) = 0: d(T_k(z)) = sd^k(z) - z
  have h_dTz : d1.hom (T_k1.hom z) = sd_k1.hom z - z := by
    rw [h_z_cycle] at h_eq1 ; simp at h_eq1 ; exact h_eq1
  -- sd is a chain map: d(sd^k(b)) = sd^k(d(b)) = sd^k(z)
  have h_sd_chainMap : sd_k2 ≫ d1 = d1 ≫ sd_k1 :=
    sd_mathlib_iter_chainMap X k (n + 1)
  have h_d_sd : d1.hom (sd_k2.hom b) = sd_k1.hom z := by
    have h : (sd_k2 ≫ d1).hom b = (d1 ≫ sd_k1).hom b := by rw [h_sd_chainMap]
    have h2 : (sd_k2 ≫ d1).hom b = d1.hom (sd_k2.hom b) := by
      simp
    have h3 : (d1 ≫ sd_k1).hom b = sd_k1.hom (d1.hom b) := by
      simp
    rw [h2, h3] at h
    rw [hz] at h
    exact h
  -- Main calculation: d(sd^k(b) - T_k(z)) = d(sd^k(b)) - d(T_k(z)) = sd^k(z) - (sd^k(z) - z) = z
  have h_main : d1.hom (sd_k2.hom b - T_k1.hom z) = z := by
    have h_lin : d1.hom (sd_k2.hom b - T_k1.hom z) =
        d1.hom (sd_k2.hom b) - d1.hom (T_k1.hom z) := by
      rw [map_sub]
    rw [h_lin, h_d_sd, h_dTz]
    ; abel
  exact h_main.symm

/-!
### Full small chain theorem

Given a subcomplex of "small" chains, assuming sd preserves small chains,
T preserves small chains, and iterates of sd eventually make any chain small,
then the inclusion of small chains into all chains induces isomorphisms on homology.

We state this in terms of element-wise properties (since we work with AddCommGrpCat).
The geometric preservation facts are assumed as hypotheses.
-/

section SmallChainTheorem

variable
  -- Predicate for "small" chains at each degree
  (isSmall : ∀ n, ((singularSSet X).chainComplex ZGrp).X n → Prop)
  -- Small chains form a submodule
  (isSmall_add : ∀ n {x y}, isSmall n x → isSmall n y → isSmall n (x + y))
  (isSmall_neg : ∀ n {x}, isSmall n x → isSmall n (-x))
  (isSmall_zero : ∀ n, isSmall n (0 : ((singularSSet X).chainComplex ZGrp).X n))
  -- The differential maps small chains to small chains (subcomplex property)
  (d_preserves_small : ∀ n {x}, isSmall (n + 1) x →
    isSmall n ((((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom x))
  -- sd preserves small chains
  (sd_preserves_small : ∀ n {x}, isSmall n x →
    isSmall n ((sd_mathlib X n).hom x))
  -- T preserves small chains
  (T_preserves_small : ∀ n {x}, isSmall n x →
    isSmall (n + 1) ((T_mathlib X n).hom x))
  -- Iterated sd preserves small chains
  (sd_iter_preserves_small : ∀ k n {x}, isSmall n x →
    isSmall n ((sd_mathlib_iter X k n).hom x))
  -- Iterated T preserves small chains
  (T_iter_preserves_small : ∀ k n {x}, isSmall n x →
    isSmall (n + 1) ((T_mathlib_iter X k n).hom x))
  -- Eventually small: for any chain, some iterate of sd makes it small
  (eventually_small : ∀ n (x : ((singularSSet X).chainComplex ZGrp).X n),
    ∃ k : ℕ, isSmall n ((sd_mathlib_iter X k n).hom x))

include isSmall isSmall_add isSmall_neg isSmall_zero
include d_preserves_small sd_preserves_small T_preserves_small
include sd_iter_preserves_small T_iter_preserves_small eventually_small

omit isSmall_add isSmall_neg isSmall_zero d_preserves_small sd_preserves_small T_preserves_small sd_iter_preserves_small T_iter_preserves_small in
/-- **Surjectivity on homology:**
Every cycle is homologous to a small cycle. -/
theorem smallChain_surjectivity (n : ℕ)
    (z : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hz_cycle : (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom z = 0) :
    ∃ (y : ((singularSSet X).chainComplex ZGrp).X (n + 1)),
      isSmall (n + 1) y ∧
      (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom y = 0 ∧
      ∃ (c : ((singularSSet X).chainComplex ZGrp).X (n + 2)),
        (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = z - y := by
  have h_eventually : ∃ k : ℕ, isSmall (n + 1) ((sd_mathlib_iter X k (n + 1)).hom z) :=
    eventually_small (n + 1) z
  rcases h_eventually with ⟨k, hk_small⟩
  let y := (sd_mathlib_iter X k (n + 1)).hom z
  have hy_small : isSmall (n + 1) y := hk_small
  have hy_cycle : (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom y = 0 := by
    dsimp only [y]
    let d_n := ((singularSSet X).chainComplex ZGrp).d (n + 1) n
    let sd_k_n1 := sd_mathlib_iter X k (n + 1)
    let sd_k_n := sd_mathlib_iter X k n
    have h_comm : sd_k_n1 ≫ d_n = d_n ≫ sd_k_n := sd_mathlib_iter_chainMap X k n
    have h1 : d_n.hom (sd_k_n1.hom z) = (sd_k_n1 ≫ d_n).hom z := by
      simp
    have h2 : (sd_k_n1 ≫ d_n).hom z = (d_n ≫ sd_k_n).hom z := by rw [h_comm]
    have h3 : (d_n ≫ sd_k_n).hom z = sd_k_n.hom (d_n.hom z) := by
      simp
    rw [h1, h2, h3, hz_cycle]
    ; simp
  let c := -((T_mathlib_iter X k (n + 1)).hom z)
  have h_eq : (sd_mathlib_iter X k (n + 1)).hom z - z =
      (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom
        ((T_mathlib_iter X k (n + 1)).hom z) :=
    sd_iter_homotopy_on_cycles X k n z hz_cycle
  have h_main : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = z - y := by
    dsimp only [c, y]
    have h_neg : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom
          (-((T_mathlib_iter X k (n + 1)).hom z)) =
        -(((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom
          ((T_mathlib_iter X k (n + 1)).hom z) := by
      rw [map_neg]
    rw [h_neg]
    rw [←h_eq]
    ; abel
  exact ⟨y, hy_small, hy_cycle, c, h_main⟩

omit isSmall_zero d_preserves_small sd_preserves_small T_preserves_small sd_iter_preserves_small in
/-- **Injectivity on homology:**
If a small cycle bounds in the full complex, it bounds in the small complex. -/
theorem smallChain_injectivity (n : ℕ)
    (y : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hy_small : isSmall (n + 1) y)
    (b : ((singularSSet X).chainComplex ZGrp).X (n + 2))
    (hb : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom b = y) :
    ∃ (c : ((singularSSet X).chainComplex ZGrp).X (n + 2)),
      isSmall (n + 2) c ∧
      (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = y := by
  have h_eventually : ∃ k : ℕ, isSmall (n + 2) ((sd_mathlib_iter X k (n + 2)).hom b) :=
    eventually_small (n + 2) b
  rcases h_eventually with ⟨k, hk_small⟩
  let sd_k_b := (sd_mathlib_iter X k (n + 2)).hom b
  let T_k_y := (T_mathlib_iter X k (n + 1)).hom y
  let c := sd_k_b + (-T_k_y)
  have h1 : isSmall (n + 2) sd_k_b := hk_small
  have h2 : isSmall (n + 2) T_k_y := T_iter_preserves_small k (n + 1) hy_small
  have hc_small : isSmall (n + 2) c := by
    have h_neg : isSmall (n + 2) (-T_k_y) := isSmall_neg (n + 2) h2
    exact isSmall_add (n + 2) h1 h_neg
  have h_main : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = y := by
    dsimp only [c, sd_k_b, T_k_y]
    have h_sub : sd_k_b - T_k_y = sd_k_b + (-T_k_y) := by abel
    have h : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom (sd_k_b - T_k_y) = y :=
      (sd_iter_boundary_decomposition X k n b y hb).symm
    have h' : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c =
        (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom (sd_k_b - T_k_y) := by
      rw [h_sub]
    rw [h']
    exact h
  exact ⟨c, hc_small, h_main⟩

end SmallChainTheorem

end MathlibComparison

-- ============================================
-- Concrete small chain theorem on Mathlib chains
-- ============================================

section ConcreteSmallChainTransfer

open CategoryTheory Limits Simplicial SSet
open TopCat (toSSet)
open SingularChain

variable {X : Type} [PseudoMetricSpace X]
variable {ι : Type*} {K : Set X}
variable (𝒰 : ι → Set X)

/-- Each face of a 𝒰-small simplex is 𝒰-small. -/
lemma face_preserves_small {n : ℕ} (i : Fin (n + 2))
    {σ : SingularSimplex X (n + 1)} (h : IsSmallWithRespectTo 𝒰 σ) :
    IsSmallWithRespectTo 𝒰 (face i σ) := by
  rcases h with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have h1 : Set.range (face i σ).val ⊆ Set.range σ.val := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact ⟨(stdSimplex.faceMap i x), by
      dsimp only [face]
      ; rfl⟩
  exact Set.Subset.trans h1 hj

/-- The boundary of a 𝒰-small chain is 𝒰-small. -/
lemma d_preserves_small_finsupp (n : ℕ) {c : SingularChain ℤ X (n + 1)}
    (h : AllSmall 𝒰 c) : AllSmall 𝒰 (SingularChain.d n c) := by
  let P : SingularChain ℤ X (n + 1) → Prop := fun c' =>
    AllSmall 𝒰 c' → AllSmall 𝒰 (SingularChain.d n c')
  have h_zero : P 0 := by
    dsimp only [P]
    intro _
    simpa [SingularChain.d] using allSmall_zero
  have h_add : ∀ (σ : SingularSimplex X (n + 1)) (r : ℤ) (c' : SingularChain ℤ X (n + 1)),
      σ ∉ Finsupp.support c' → r ≠ 0 → P c' → P (Finsupp.single σ r + c') := by
    intro σ r c' hσ_notin hr ih
    dsimp only [P] at *
    intro h_all
    have h_sum : SingularChain.d n (Finsupp.single σ r + c') =
        SingularChain.d n (Finsupp.single σ r) + SingularChain.d n c' :=
      SingularChain.d_add n (Finsupp.single σ r) c'
    rw [h_sum]
    have h_c0_small : AllSmall 𝒰 c' := by
      intro τ hτ
      exact h_all τ (by
        have h_ne : c' τ ≠ 0 := Finsupp.mem_support_iff.mp hτ
        have h_contra : τ ≠ σ := by
          intro h_eq
          rw [h_eq] at h_ne
          exact Finsupp.mem_support_iff.not.mp hσ_notin h_ne
        have h_sum_ne : (Finsupp.single σ r + c') τ ≠ 0 := by
          have h4 : (Finsupp.single σ r) τ = 0 := by
            rw [Finsupp.single_apply_eq_zero]
            intro h_eq
            exfalso
            exact h_contra h_eq
          rw [Finsupp.add_apply, h4, zero_add]
          exact h_ne
        exact Finsupp.mem_support_iff.mpr h_sum_ne)
    have h_ih : AllSmall 𝒰 (SingularChain.d n c') := ih h_c0_small
    have hσ_in : σ ∈ Finsupp.support (Finsupp.single σ r + c') := by
      have h_coeff : (Finsupp.single σ r + c') σ = r := by
        have h1 : (Finsupp.single σ r + c') σ = (Finsupp.single σ r) σ + c' σ := Finsupp.add_apply _ _ _
        rw [h1]
        have h2 : (Finsupp.single σ r) σ = r := by simp
        have h3 : c' σ = 0 := by simpa [Finsupp.mem_support_iff] using hσ_notin
        rw [h2, h3, add_zero]
      have h_ne_zero : (Finsupp.single σ r + c') σ ≠ 0 := by
        rw [h_coeff]; exact hr
      exact Finsupp.mem_support_iff.mpr h_ne_zero
    have hσ_small : IsSmallWithRespectTo 𝒰 σ := h_all σ hσ_in
    have h_faces_small : ∀ (i : Fin (n + 2)),
        AllSmall 𝒰 ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ)) := by
      intro i
      apply allSmall_smul
      have h_face_small : AllSmall 𝒰 (Finsupp.single (face i σ) (1 : ℤ)) := by
        exact allSmall_single (face_preserves_small 𝒰 i hσ_small)
      exact h_face_small
    have h_sum_small : AllSmall 𝒰 (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ)) := by
      have h_main : ∀ (s : Finset (Fin (n + 2))),
          (∀ i ∈ s, AllSmall 𝒰 ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ))) →
          AllSmall 𝒰 (∑ i ∈ s, (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ)) := by
        intro s
        induction s using Finset.induction with
        | empty =>
          intro _
          simpa using allSmall_zero
        | @insert i s hi ih =>
          intro h_all
          have h1 : AllSmall 𝒰 ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ)) :=
            h_all i (Finset.mem_insert_self i s)
          have h2 : AllSmall 𝒰 (∑ j ∈ s, (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (face j σ) (1 : ℤ)) :=
            ih (fun j hj => h_all j (Finset.mem_insert_of_mem hj))
          rw [Finset.sum_insert hi]
          exact allSmall_add h1 h2
      exact h_main Finset.univ (fun i _ => h_faces_small i)
    have h_single_small : AllSmall 𝒰 (SingularChain.d n (Finsupp.single σ r)) := by
      have h_d_single : SingularChain.d n (Finsupp.single σ r) =
          r • (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (face i σ) (1 : ℤ)) := by
        simp [SingularChain.d]
      rw [h_d_single]
      exact allSmall_smul h_sum_small
    exact allSmall_add h_single_small h_ih
  exact Finsupp.induction c h_zero h_add h

/-- sd_mathlib_iter corresponds to sdIter via mathlibToFinsupp. -/
lemma sd_mathlib_iter_via_finsupp (k n : ℕ)
    (x : ((singularSSet X).chainComplex ZGrp).X n) :
    (mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x) =
    sdIter k n ((mathlibToFinsupp X n).hom x) := by
  induction k with
  | zero =>
    dsimp only [sd_mathlib_iter, sdIter]
    ; simp
  | succ k ih =>
    have h1 : (sd_mathlib_iter X (k + 1) n).hom x =
        (sd_mathlib X n).hom ((sd_mathlib_iter X k n).hom x) := by
      dsimp only [sd_mathlib_iter]
      ; simp
    rw [h1]
    have h2 : (mathlibToFinsupp X n).hom ((sd_mathlib X n).hom ((sd_mathlib_iter X k n).hom x)) =
        sdMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
      dsimp only [sd_mathlib]
      have h_comp : (mathlibToFinsupp X n).hom ((finsuppToMathlib X n).hom
          (sdMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)))) =
          sdMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
        have h_inv : (finsuppToMathlib X n ≫ mathlibToFinsupp X n).hom
            (sdMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x))) =
            sdMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
          rw [mathlibToFinsupp_leftInverse X n]
          ; rfl
        simpa [AddCommGrpCat.comp_apply] using h_inv
      simpa [AddCommGrpCat.comp_apply] using h_comp
    rw [h2, ih]
    have h3 : sdMap n (sdIter k n ((mathlibToFinsupp X n).hom x)) =
        sdIter (k + 1) n ((mathlibToFinsupp X n).hom x) := by
      exact (sdIter_succ k n ((mathlibToFinsupp X n).hom x)).symm
    exact h3

/-- T_mathlib_iter corresponds to TIter via mathlibToFinsupp. -/
lemma T_mathlib_iter_via_finsupp (k n : ℕ)
    (x : ((singularSSet X).chainComplex ZGrp).X n) :
    (mathlibToFinsupp X (n + 1)).hom ((T_mathlib_iter X k n).hom x) =
    TIter k n ((mathlibToFinsupp X n).hom x) := by
  induction k with
  | zero =>
    dsimp only [T_mathlib_iter, TIter]
    ; simp
  | succ k ih =>
    have h1 : (T_mathlib_iter X (k + 1) n).hom x =
        (T_mathlib_iter X k n).hom x +
        (T_mathlib X n).hom ((sd_mathlib_iter X k n).hom x) := by
      dsimp only [T_mathlib_iter]
      ; simp
    rw [h1]
    have h2 : (mathlibToFinsupp X (n + 1)).hom
        ((T_mathlib_iter X k n).hom x + (T_mathlib X n).hom ((sd_mathlib_iter X k n).hom x)) =
        (mathlibToFinsupp X (n + 1)).hom ((T_mathlib_iter X k n).hom x) +
        (mathlibToFinsupp X (n + 1)).hom ((T_mathlib X n).hom ((sd_mathlib_iter X k n).hom x)) := by
      exact map_add (mathlibToFinsupp X (n + 1)).hom _ _
    rw [h2]
    have h3 : (mathlibToFinsupp X (n + 1)).hom ((T_mathlib X n).hom ((sd_mathlib_iter X k n).hom x)) =
        TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
      dsimp only [T_mathlib]
      have h_comp : (mathlibToFinsupp X (n + 1)).hom ((finsuppToMathlib X (n + 1)).hom
          (TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)))) =
          TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
        have h_inv : (finsuppToMathlib X (n + 1) ≫ mathlibToFinsupp X (n + 1)).hom
            (TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x))) =
            TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) := by
          rw [mathlibToFinsupp_leftInverse X (n + 1)] ; rfl
        simpa [AddCommGrpCat.comp_apply] using h_inv
      simpa [AddCommGrpCat.comp_apply] using h_comp
    rw [h3, ih]
    have h4 : TMap n ((mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x)) =
        TMap n (sdIter k n ((mathlibToFinsupp X n).hom x)) := by
      rw [sd_mathlib_iter_via_finsupp k n x]
    rw [h4]
    ; rfl

/-- Small chains on Mathlib side: chains whose Finsupp counterpart is AllSmall. -/
def isSmall_mlib (n : ℕ) (x : ((singularSSet X).chainComplex ZGrp).X n) : Prop :=
  AllSmall 𝒰 ((mathlibToFinsupp X n).hom x)

/-- isSmall_mlib is preserved under addition. -/
lemma isSmall_mlib_add (n : ℕ) {x y : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) (hy : isSmall_mlib 𝒰 n y) :
    isSmall_mlib 𝒰 n (x + y) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom (x + y) =
      (mathlibToFinsupp X n).hom x + (mathlibToFinsupp X n).hom y := by
    exact map_add (mathlibToFinsupp X n).hom x y
  rw [h]
  exact allSmall_add hx hy

/-- isSmall_mlib is preserved under negation. -/
lemma isSmall_mlib_neg (n : ℕ) {x : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) :
    isSmall_mlib 𝒰 n (-x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom (-x) = -((mathlibToFinsupp X n).hom x) := by
    exact map_neg (mathlibToFinsupp X n).hom x
  rw [h]
  exact allSmall_neg hx

/-- Zero is small. -/
lemma isSmall_mlib_zero (n : ℕ) :
    isSmall_mlib 𝒰 n (0 : ((singularSSet X).chainComplex ZGrp).X n) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom (0 : ((singularSSet X).chainComplex ZGrp).X n) = 0 := by
    exact map_zero (mathlibToFinsupp X n).hom
  rw [h]
  exact allSmall_zero

/-- The differential preserves small chains. -/
lemma d_preserves_small_mlib (n : ℕ)
    {x : ((singularSSet X).chainComplex ZGrp).X (n + 1)}
    (hx : isSmall_mlib 𝒰 (n + 1) x) :
    isSmall_mlib 𝒰 n ((((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom ((((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom x) =
      SingularChain.d n ((mathlibToFinsupp X (n + 1)).hom x) := by
    have h_chainMap : ((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n =
        mathlibToFinsupp X (n + 1) ≫ d_morphism X n :=
      mathlibToFinsupp_chainMap X n
    have h2 : (((singularSSet X).chainComplex ZGrp).d (n + 1) n ≫ mathlibToFinsupp X n).hom x =
        (mathlibToFinsupp X (n + 1) ≫ d_morphism X n).hom x := by rw [h_chainMap]
    simpa [AddCommGrpCat.comp_apply, d_morphism, d_addMap] using h2
  rw [h]
  exact d_preserves_small_finsupp 𝒰 n hx

/-- sd_mathlib preserves small chains. -/
lemma sd_preserves_small_mlib (n : ℕ)
    {x : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) :
    isSmall_mlib 𝒰 n ((sd_mathlib X n).hom x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom ((sd_mathlib X n).hom x) =
      sdMap n ((mathlibToFinsupp X n).hom x) := by
    dsimp only [sd_mathlib]
    have h_comp : (mathlibToFinsupp X n).hom ((finsuppToMathlib X n).hom
        (sdMap n ((mathlibToFinsupp X n).hom x))) =
        sdMap n ((mathlibToFinsupp X n).hom x) := by
      have h_inv : (finsuppToMathlib X n ≫ mathlibToFinsupp X n).hom
          (sdMap n ((mathlibToFinsupp X n).hom x)) =
          sdMap n ((mathlibToFinsupp X n).hom x) := by
        rw [mathlibToFinsupp_leftInverse X n] ; rfl
      simpa [AddCommGrpCat.comp_apply] using h_inv
    simpa [AddCommGrpCat.comp_apply] using h_comp
  rw [h]
  exact sd_preserves_small n hx

/-- T_mathlib preserves small chains. -/
lemma T_preserves_small_mlib (n : ℕ)
    {x : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) :
    isSmall_mlib 𝒰 (n + 1) ((T_mathlib X n).hom x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X (n + 1)).hom ((T_mathlib X n).hom x) =
      TMap n ((mathlibToFinsupp X n).hom x) := by
    dsimp only [T_mathlib]
    have h_comp : (mathlibToFinsupp X (n + 1)).hom ((finsuppToMathlib X (n + 1)).hom
        (TMap n ((mathlibToFinsupp X n).hom x))) =
        TMap n ((mathlibToFinsupp X n).hom x) := by
      have h_inv : (finsuppToMathlib X (n + 1) ≫ mathlibToFinsupp X (n + 1)).hom
          (TMap n ((mathlibToFinsupp X n).hom x)) =
          TMap n ((mathlibToFinsupp X n).hom x) := by
        rw [mathlibToFinsupp_leftInverse X (n + 1)] ; rfl
      simpa [AddCommGrpCat.comp_apply] using h_inv
    simpa [AddCommGrpCat.comp_apply] using h_comp
  rw [h]
  exact T_preserves_small n hx

/-- Iterated sd preserves small chains. -/
lemma sd_iter_preserves_small_mlib (k n : ℕ)
    {x : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) :
    isSmall_mlib 𝒰 n ((sd_mathlib_iter X k n).hom x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x) =
      sdIter k n ((mathlibToFinsupp X n).hom x) :=
    sd_mathlib_iter_via_finsupp k n x
  rw [h]
  exact sdIter_preserves_small 𝒰 k n hx

/-- Iterated T preserves small chains. -/
lemma T_iter_preserves_small_mlib (k n : ℕ)
    {x : ((singularSSet X).chainComplex ZGrp).X n}
    (hx : isSmall_mlib 𝒰 n x) :
    isSmall_mlib 𝒰 (n + 1) ((T_mathlib_iter X k n).hom x) := by
  dsimp only [isSmall_mlib]
  have h : (mathlibToFinsupp X (n + 1)).hom ((T_mathlib_iter X k n).hom x) =
      TIter k n ((mathlibToFinsupp X n).hom x) :=
    T_mathlib_iter_via_finsupp k n x
  rw [h]
  exact TIter_preserves_small 𝒰 k n hx

/-- Eventually small: iterated sd makes any chain with image in K small. -/
lemma eventually_small_mlib (hK : IsCompact K) (hU : ∀ i, IsOpen (𝒰 i)) (hcover : K ⊆ ⋃ i, 𝒰 i)
    (n : ℕ) (hn : 0 < n)
    (x : ((singularSSet X).chainComplex ZGrp).X n)
    (hx_images : ∀ σ ∈ Finsupp.support ((mathlibToFinsupp X n).hom x), Set.range σ.val ⊆ K) :
    ∃ k : ℕ, isSmall_mlib 𝒰 n ((sd_mathlib_iter X k n).hom x) := by
  dsimp only [isSmall_mlib]
  have h_main : ∃ k : ℕ, AllSmall 𝒰 (sdIter k n ((mathlibToFinsupp X n).hom x)) :=
    geometric_small_chain_finite (hK := hK) (hU := hU) (hcover := hcover)
      (n := n) (hn := hn)
      (c := (mathlibToFinsupp X n).hom x) (hc := hx_images)
  rcases h_main with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have h : (mathlibToFinsupp X n).hom ((sd_mathlib_iter X k n).hom x) =
      sdIter k n ((mathlibToFinsupp X n).hom x) :=
    sd_mathlib_iter_via_finsupp k n x
  rw [h]
  exact hk

/-- The image of a singular simplex is compact. -/
lemma singularSimplex_range_compact {n : ℕ} (σ : SingularSimplex X n) :
    IsCompact (Set.range σ.val) :=
  isCompact_range σ.2

/-- The union of simplex images in a chain's support is compact. -/
lemma chain_support_union_compact {n : ℕ} (c : SingularChain ℤ X n) :
    IsCompact (⋃ σ ∈ Finsupp.support c, Set.range σ.val) :=
  Finset.isCompact_biUnion (Finsupp.support c) fun σ _ => singularSimplex_range_compact σ

/-- For n = 0, every chain is 𝒰-small when 𝒰 covers X. -/
lemma allSmall_zero_dim (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) :
    ∀ (c : SingularChain ℤ X 0), AllSmall 𝒰 c := by
  intro c σ hσ
  let α := {x : Fin 1 → ℝ // x ∈ stdSimplex ℝ (Fin 1)}
  have h_subsingleton : Subsingleton α := by
    exact stdSimplex.instSubsingletonElemForall
  have h_nonempty : Nonempty α := by
    exact stdSimplex.instNonemptyElemForall
  have h1 : ∃ (x₀ : X), Set.range σ.val = {x₀} := by
    rcases h_nonempty with ⟨a₀⟩
    refine ⟨σ.val a₀, ?_⟩
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      have h_eq : a = a₀ := Subsingleton.elim a a₀
      rw [h_eq]
    · intro h
      rw [h]
      exact ⟨a₀, rfl⟩
  rcases h1 with ⟨x, hx⟩
  have h_x_in_univ : x ∈ (Set.univ : Set X) := by simp
  have h_x_in_union' : x ∈ ⋃ (j : ι), 𝒰 j := hcover h_x_in_univ
  have h_exists : ∃ (j : ι), x ∈ 𝒰 j := by
    exact Set.mem_iUnion.mp (hcover h_x_in_univ)
  rcases h_exists with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [hx]
  simpa using hj

/-- Full eventually small: iterated sd makes any chain small,
    for any open cover of X. -/
theorem eventually_small_full (hU : ∀ i, IsOpen (𝒰 i)) (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) :
    ∀ (n : ℕ) (x : ((singularSSet X).chainComplex ZGrp).X n),
    ∃ k : ℕ, isSmall_mlib 𝒰 n ((sd_mathlib_iter X k n).hom x) := by
  intro n x
  by_cases hn : n = 0
  · -- n = 0: every chain is already small
    subst hn
    refine ⟨0, ?_⟩
    dsimp only [isSmall_mlib, sd_mathlib_iter]
    simpa using allSmall_zero_dim 𝒰 hcover ((mathlibToFinsupp X 0).hom x)
  · -- n > 0: use compact support argument
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let c := (mathlibToFinsupp X n).hom x
    let K := ⋃ σ ∈ Finsupp.support c, Set.range σ.val
    have hK_compact : IsCompact K := chain_support_union_compact c
    have hK_cover : K ⊆ ⋃ i, 𝒰 i := by
      intro y hy
      have h_mem : ∃ σ ∈ Finsupp.support c, y ∈ Set.range σ.val := by
        simpa [K] using hy
      rcases h_mem with ⟨σ, hσ_support, hy_range⟩
      have h1 : Set.range σ.val ⊆ (Set.univ : Set X) := by simp
      have h2 : Set.range σ.val ⊆ ⋃ i, 𝒰 i := Set.Subset.trans h1 hcover
      exact h2 hy_range
    have h_images : ∀ σ ∈ Finsupp.support c, Set.range σ.val ⊆ K := by
      intro σ hσ y hy
      exact Set.subset_biUnion_of_mem hσ hy
    exact eventually_small_mlib 𝒰 hK_compact hU hK_cover n hn_pos x h_images

/-- Concrete small chain theorem: surjectivity on homology. -/
theorem concrete_smallChain_surjectivity (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) (n : ℕ)
    (z : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hz_cycle : (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom z = 0) :
    ∃ (y : ((singularSSet X).chainComplex ZGrp).X (n + 1)),
      isSmall_mlib 𝒰 (n + 1) y ∧
      (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom y = 0 ∧
      ∃ (c : ((singularSSet X).chainComplex ZGrp).X (n + 2)),
        (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = z - y :=
  smallChain_surjectivity X
    (isSmall := fun n => isSmall_mlib 𝒰 n)
    (eventually_small := eventually_small_full 𝒰 hU hcover)
    n z hz_cycle

/-- Concrete small chain theorem: injectivity on homology. -/
theorem concrete_smallChain_injectivity (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) (n : ℕ)
    (y : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hy_small : isSmall_mlib 𝒰 (n + 1) y)
    (b : ((singularSSet X).chainComplex ZGrp).X (n + 2))
    (hb : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom b = y) :
    ∃ (c : ((singularSSet X).chainComplex ZGrp).X (n + 2)),
      isSmall_mlib 𝒰 (n + 2) c ∧
      (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c = y :=
  smallChain_injectivity X
    (isSmall := fun n => isSmall_mlib 𝒰 n)
    (isSmall_add := fun n => isSmall_mlib_add 𝒰 n)
    (isSmall_neg := fun n {x} hx => by
      dsimp only [isSmall_mlib]
      have h : (mathlibToFinsupp X n).hom (-x) = -((mathlibToFinsupp X n).hom x) := by
        rw [map_neg]
      rw [h]
      exact allSmall_neg hx)
    (T_iter_preserves_small := fun k n {x} hx => T_iter_preserves_small_mlib 𝒰 k n hx)
    (eventually_small := eventually_small_full 𝒰 hU hcover)
    n y hy_small b hb

end ConcreteSmallChainTransfer

-- ============================================
-- IsIso upgrade: element-wise → IsIso(homologyMap)
-- ============================================

section IsIsoUpgrade

open CategoryTheory
open CategoryTheory.ShortComplex

/-- Auxiliary: element-wise surjectivity + injectivity on a short complex
    of abelian groups implies the homology map is an isomorphism. -/
theorem shortComplex_quasiIso_of_elementwise
    {S₁ S₂ : ShortComplex AddCommGrpCat}
    (φ : S₁ ⟶ S₂)
    (h_surj : ∀ (z : S₂.X₂), S₂.g.hom z = 0 →
      ∃ (y : S₁.X₂), S₁.g.hom y = 0 ∧
        ∃ (c : S₂.X₁), S₂.f.hom c = z - φ.τ₂.hom y)
    (h_inj : ∀ (y : S₁.X₂), S₁.g.hom y = 0 →
      (∃ (b : S₂.X₁), S₂.f.hom b = φ.τ₂.hom y) →
      ∃ (c : S₁.X₁), S₁.f.hom c = y)
    [S₁.HasHomology] [S₂.HasHomology] :
    IsIso (ShortComplex.homologyMap φ) := by
  let h₁ := S₁.abLeftHomologyData
  let h₂ := S₂.abLeftHomologyData
  let γ : LeftHomologyMapData φ h₁ h₂ := by exact leftHomologyMapData φ h₁ h₂
  let K₁ := AddMonoidHom.ker S₁.g.hom
  let B₁ := AddMonoidHom.range S₁.abToCycles
  let K₂ := AddMonoidHom.ker S₂.g.hom
  let B₂ := AddMonoidHom.range S₂.abToCycles
  let Q₁ := AddCommGrpCat.of (K₁ ⧸ B₁)
  let Q₂ := AddCommGrpCat.of (K₂ ⧸ B₂)
  let e₁ : S₁.homology ≅ Q₁ := S₁.abHomologyIso
  let e₂ : S₂.homology ≅ Q₂ := S₂.abHomologyIso
  -- ψ is the concrete map on quotient homology groups
  let ψ : Q₁ ⟶ Q₂ := e₁.inv ≫ ShortComplex.homologyMap φ ≫ e₂.hom
  -- ψ equals γ.φH (the φH component of the LeftHomologyMapData)
  have h_e₁_def : e₁ = h₁.homologyIso := by rfl
  have h_e₂_def : e₂ = h₂.homologyIso := by rfl
  have hψ_eq : ψ = γ.φH := by
    dsimp only [ψ]
    rw [h_e₁_def, h_e₂_def, γ.homologyMap_eq]
    have h1 : h₁.homologyIso.inv ≫ h₁.homologyIso.hom = 𝟙 _ := h₁.homologyIso.inv_hom_id
    have h2 : h₂.homologyIso.inv ≫ h₂.homologyIso.hom = 𝟙 _ := h₂.homologyIso.inv_hom_id
    calc
      h₁.homologyIso.inv ≫ (h₁.homologyIso.hom ≫ γ.φH ≫ h₂.homologyIso.inv) ≫ h₂.homologyIso.hom
        = (h₁.homologyIso.inv ≫ h₁.homologyIso.hom) ≫ γ.φH ≫ (h₂.homologyIso.inv ≫ h₂.homologyIso.hom) := by
          simp [Category.assoc]
      _ = 𝟙 _ ≫ γ.φH ≫ 𝟙 _ := by rw [h1, h2]
      _ = γ.φH := by simp
  -- γ.φK maps cycles to cycles by restricting φ.τ₂
  have h_commi : ∀ (x : h₁.K), h₂.i.hom (γ.φK.hom x) = φ.τ₂.hom (h₁.i.hom x) := by
    intro x
    have h : (γ.φK ≫ h₂.i).hom x = (h₁.i ≫ φ.τ₂).hom x := by
      rw [γ.commi]
    exact h
  -- γ.φH commutes with the quotient maps
  have h_commπ : ∀ (x : h₁.K), γ.φH.hom (h₁.π.hom x) = h₂.π.hom (γ.φK.hom x) := by
    intro x
    have h : (h₁.π ≫ γ.φH).hom x = (γ.φK ≫ h₂.π).hom x := by
      rw [γ.commπ]
    exact h
  -- The quotient map π is surjective
  have hπ₁_surj : Function.Surjective h₁.π.hom := by
    intro q
    exact Quotient.exists_rep q
  have hπ₂_surj : Function.Surjective h₂.π.hom := by
    intro q
    exact Quotient.exists_rep q
  -- abToCycles x is the cycle ⟨S.f x, _⟩
  have h_abToCycles_val₁ : ∀ (x : S₁.X₁),
      h₁.i.hom (S₁.abToCycles x) = S₁.f.hom x := by
    intro x
    rfl
  have h_abToCycles_val₂ : ∀ (x : S₂.X₁),
      h₂.i.hom (S₂.abToCycles x) = S₂.f.hom x := by
    intro x
    rfl
  -- An element of K₂ is in B₂ iff it's of the form S₂.f b for some b
  have h_mem_B₂_iff : ∀ (z : K₂), z ∈ B₂ ↔ ∃ (b : S₂.X₁), S₂.f.hom b = h₂.i.hom z := by
    intro z
    constructor
    · intro hz
      rcases hz with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      have h : h₂.i.hom (S₂.abToCycles b) = S₂.f.hom b := h_abToCycles_val₂ b
      have h' : S₂.abToCycles b = z := hb
      rw [← h, h']
    · rintro ⟨b, hb⟩
      have h_i_inj : Function.Injective h₂.i.hom := by
        exact (AddCommGrpCat.mono_iff_injective h₂.i).mp (by infer_instance)
      have h_eq : S₂.abToCycles b = z := by
        apply h_i_inj
        have h : h₂.i.hom (S₂.abToCycles b) = S₂.f.hom b := h_abToCycles_val₂ b
        rw [h, hb]
      exact ⟨b, h_eq⟩
  have h_mem_B₁_iff : ∀ (y : K₁), y ∈ B₁ ↔ ∃ (c : S₁.X₁), S₁.f.hom c = h₁.i.hom y := by
    intro y
    constructor
    · intro hy
      rcases hy with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have h : h₁.i.hom (S₁.abToCycles c) = S₁.f.hom c := h_abToCycles_val₁ c
      have h' : S₁.abToCycles c = y := hc
      rw [← h, h']
    · rintro ⟨c, hc⟩
      have h_i_inj : Function.Injective h₁.i.hom := by
        exact (AddCommGrpCat.mono_iff_injective h₁.i).mp (by infer_instance)
      have h_eq : S₁.abToCycles c = y := by
        apply h_i_inj
        have h : h₁.i.hom (S₁.abToCycles c) = S₁.f.hom c := h_abToCycles_val₁ c
        rw [h, hc]
      exact ⟨c, h_eq⟩
  -- Equality in Q₁: π y = π y' ↔ y - y' ∈ B₁
  have h_eq_Q₁ : ∀ (y y' : K₁), h₁.π.hom y = h₁.π.hom y' ↔ y - y' ∈ B₁ := by
    intro y y'
    exact QuotientAddGroup.eq_iff_sub_mem
  have h_eq_Q₂ : ∀ (z z' : K₂), h₂.π.hom z = h₂.π.hom z' ↔ z - z' ∈ B₂ := by
    intro z z'
    exact QuotientAddGroup.eq_iff_sub_mem
  -- Injectivity of γ.φH
  have h_inj' : Function.Injective γ.φH.hom := by
    intro q₁ q₁' h_eq
    rcases hπ₁_surj q₁ with ⟨y, rfl⟩
    rcases hπ₁_surj q₁' with ⟨y', rfl⟩
    have h1 : h₂.π.hom (γ.φK.hom y) = h₂.π.hom (γ.φK.hom y') := by
      rw [← h_commπ y, ← h_commπ y', h_eq]
    have h2 : γ.φK.hom y - γ.φK.hom y' ∈ B₂ := (h_eq_Q₂ (γ.φK.hom y) (γ.φK.hom y')).mp h1
    have h3 : ∃ (b : S₂.X₁), S₂.f.hom b = h₂.i.hom (γ.φK.hom y - γ.φK.hom y') :=
      (h_mem_B₂_iff (γ.φK.hom y - γ.φK.hom y')).mp h2
    rcases h3 with ⟨b, hb⟩
    have h4 : S₂.f.hom b = φ.τ₂.hom (h₁.i.hom y) - φ.τ₂.hom (h₁.i.hom y') := by
      have h5 : h₂.i.hom (γ.φK.hom y - γ.φK.hom y') =
          h₂.i.hom (γ.φK.hom y) - h₂.i.hom (γ.φK.hom y') := by
        exact map_sub h₂.i.hom _ _
      rw [h5] at hb
      rw [h_commi y, h_commi y'] at *
      ; exact hb
    have h5 : S₁.g.hom (h₁.i.hom y - h₁.i.hom y') = 0 := by
      have hy : S₁.g.hom (h₁.i.hom y) = 0 := y.prop
      have hy' : S₁.g.hom (h₁.i.hom y') = 0 := y'.prop
      simp [hy, hy']
    have h4' : S₂.f.hom b = φ.τ₂.hom (h₁.i.hom y - h₁.i.hom y') := by
      have h_map : φ.τ₂.hom (h₁.i.hom y - h₁.i.hom y') = φ.τ₂.hom (h₁.i.hom y) - φ.τ₂.hom (h₁.i.hom y') := by
        exact map_sub φ.τ₂.hom _ _
      rw [h_map]
      exact h4
    have h6 : ∃ (c : S₁.X₁), S₁.f.hom c = h₁.i.hom y - h₁.i.hom y' :=
      h_inj (h₁.i.hom y - h₁.i.hom y') h5 ⟨b, h4'⟩
    have h7 : y - y' ∈ B₁ := (h_mem_B₁_iff (y - y')).mpr h6
    have h8 : h₁.π.hom y = h₁.π.hom y' := (h_eq_Q₁ y y').mpr h7
    exact h8
  -- Surjectivity of γ.φH
  have h_surj' : Function.Surjective γ.φH.hom := by
    intro q₂
    rcases hπ₂_surj q₂ with ⟨z, rfl⟩
    let z' : S₂.X₂ := h₂.i.hom z
    have hz : S₂.g.hom z' = 0 := z.prop
    rcases h_surj z' hz with ⟨y, hy_cycle, c, hc⟩
    let yK : K₁ := ⟨y, hy_cycle⟩
    have h9 : z - γ.φK.hom yK ∈ B₂ := by
      apply (h_mem_B₂_iff (z - γ.φK.hom yK)).mpr
      refine ⟨c, ?_⟩
      have h10 : h₂.i.hom (z - γ.φK.hom yK) = z' - φ.τ₂.hom y := by
        have h11 : h₂.i.hom (z - γ.φK.hom yK) = h₂.i.hom z - h₂.i.hom (γ.φK.hom yK) := by
          exact map_sub h₂.i.hom _ _
        rw [h11, h_commi yK]
        ; rfl
      rw [h10]
      exact hc
    have h10 : h₂.π.hom z = h₂.π.hom (γ.φK.hom yK) := by
      exact (h_eq_Q₂ z (γ.φK.hom yK)).mpr h9
    refine ⟨h₁.π.hom yK, ?_⟩
    rw [h_commπ yK, h10]
  -- Conclude IsIso for γ.φH
  have h_mono : Mono γ.φH := by
    rwa [AddCommGrpCat.mono_iff_injective]
  have h_epi : Epi γ.φH := by
    rwa [AddCommGrpCat.epi_iff_surjective]
  have h_iso : IsIso γ.φH := isIso_of_mono_of_epi γ.φH
  -- Conclude IsIso for homologyMap φ
  have h_main : IsIso ψ := by
    rw [hψ_eq]
    exact h_iso
  have : IsIso (ShortComplex.homologyMap φ) := by
    have h_comp : ψ = e₁.inv ≫ ShortComplex.homologyMap φ ≫ e₂.hom := rfl
    rw [h_comp] at h_main
    have h1 : IsIso (e₁.inv ≫ (ShortComplex.homologyMap φ ≫ e₂.hom)) := h_main
    have h_e1inv_iso : IsIso e₁.inv := by infer_instance
    have h2 : IsIso (ShortComplex.homologyMap φ ≫ e₂.hom) := by
      exact IsIso.of_isIso_comp_left e₁.inv (ShortComplex.homologyMap φ ≫ e₂.hom)
    have h_e2hom_iso : IsIso e₂.hom := by infer_instance
    exact IsIso.of_isIso_comp_right (ShortComplex.homologyMap φ) e₂.hom
  exact this

end IsIsoUpgrade

-- ============================================
-- Small subcomplex for a general open cover
-- ============================================

section OpenCoverSmallSubcomplex

open CategoryTheory Limits Simplicial SSet
open TopCat (toSSet)
open SingularChain

variable {X : Type} [PseudoMetricSpace X]
variable {ι : Type*}
variable (𝒰 : ι → Set X)

/-- A singular simplex (in Mathlib's SSet sense) is 𝒰-small if its image is
    contained in some element of the cover 𝒰. -/
def isSmallSimplex_cover {n : SimplexCategoryᵒᵖ} (σ : (toSSet.obj (TopCat.of X)).obj n) : Prop :=
  ∃ (i : ι), Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n σ) ⊆ 𝒰 i

/-- The subcomplex of 𝒰-small singular simplices. -/
noncomputable def smallSubcomplex_cover : (toSSet.obj (TopCat.of X)).Subcomplex where
  obj n := {σ | isSmallSimplex_cover 𝒰 σ}
  map {m n} f σ h := by
    dsimp only [isSmallSimplex_cover] at h ⊢
    rcases h with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h_main : Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n ((toSSet.obj (TopCat.of X)).map f σ)) ⊆
        Set.range (TopCat.toSSetObjEquiv (TopCat.of X) m σ) := by
      let g : C(stdSimplex ℝ (Fin (n.unop.len + 1)), stdSimplex ℝ (Fin (m.unop.len + 1))) :=
        ⟨stdSimplex.map f.unop, stdSimplex.continuous_map f.unop⟩
      have h_eq : (TopCat.toSSetObjEquiv (TopCat.of X) n ((toSSet.obj (TopCat.of X)).map f σ)) =
          (TopCat.toSSetObjEquiv (TopCat.of X) m σ).comp g := by
        simp only [TopCat.toSSetObjEquiv]
        ; rfl
      rw [h_eq]
      intro y hy
      rcases hy with ⟨x, rfl⟩
      exact ⟨g x, rfl⟩
    exact Set.Subset.trans h_main hi

/-- The small simplicial set (of 𝒰-small simplices). -/
def smallSSet_cover : SSet := (smallSubcomplex_cover 𝒰).toSSet

/-- The inclusion of the small simplicial set into the full one. -/
def smallι_cover : smallSSet_cover 𝒰 ⟶ singularSSet X :=
  (smallSubcomplex_cover 𝒰).ι

/-- The small singular chain complex C_small(X). -/
noncomputable def smallChainComplex_cover : ChainComplex AddCommGrpCat ℕ :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj ZGrp).obj (smallSSet_cover 𝒰)

/-- The inclusion map C_small(X) → C(X) on chain complexes. -/
noncomputable def smallChainInclusion_cover :
    smallChainComplex_cover 𝒰 ⟶ (singularSSet X).chainComplex ZGrp :=
  ((SSet.chainComplexFunctor AddCommGrpCat).obj ZGrp).map (smallι_cover 𝒰)

/-- The chain complex inclusion maps small generators to full generators. -/
lemma smallChainInclusion_cover_ι (n : ℕ) (x : smallSSet_cover 𝒰 _⦋n⦌) :
    (smallSSet_cover 𝒰).ιChainComplex (R := ZGrp) x ≫ (smallChainInclusion_cover 𝒰).f n =
    (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x) := by
  simp [smallChainInclusion_cover, smallι_cover]

/-- Simplex-level equivalence of smallness notions. -/
lemma isSmallSimplex_iff_IsSmallWithRespectTo {n : ℕ}
    (σ : (singularSSet X) _⦋n⦌) :
    isSmallSimplex_cover 𝒰 σ ↔
    IsSmallWithRespectTo 𝒰 (singularSimplexEquiv X n σ) := by
  dsimp only [isSmallSimplex_cover, IsSmallWithRespectTo, singularSimplexEquiv, singularSSet]
  ; exact Iff.rfl

/-- A generator simplex is 𝒰-small iff its Finsupp counterpart is. -/
lemma isSmall_mlib_single (n : ℕ) (σ : (singularSSet X) _⦋n⦌) :
    isSmall_mlib 𝒰 n ((singularSSet X).ιChainComplex (R := ZGrp) σ (1 : ℤ)) ↔
    IsSmallWithRespectTo 𝒰 (singularSimplexEquiv X n σ) := by
  let x : singularSSet X _⦋n⦌ := σ
  have h1 : (mathlibToFinsupp X n).hom (((singularSSet X).ιChainComplex (R := ZGrp) x) (1 : ℤ)) =
      Finsupp.single (singularSimplexEquiv X n x) (1 : ℤ) := by
    exact mathlibToFinsupp_ι X n x
  have h2 : isSmall_mlib 𝒰 n ((singularSSet X).ιChainComplex (R := ZGrp) σ (1 : ℤ)) ↔
      AllSmall 𝒰 (Finsupp.single (singularSimplexEquiv X n σ) (1 : ℤ)) := by
    have h_eq : (mathlibToFinsupp X n).hom (((singularSSet X).ιChainComplex (R := ZGrp) σ) (1 : ℤ)) =
        Finsupp.single (singularSimplexEquiv X n σ) (1 : ℤ) := h1
    dsimp only [isSmall_mlib]
    rw [h_eq]
  rw [h2]
  have h3 : AllSmall 𝒰 (Finsupp.single (singularSimplexEquiv X n σ) (1 : ℤ)) ↔
      IsSmallWithRespectTo 𝒰 (singularSimplexEquiv X n σ) := by
    constructor
    · intro h
      have h4 : (singularSimplexEquiv X n σ) ∈ Finsupp.support (Finsupp.single (singularSimplexEquiv X n σ) (1 : ℤ)) := by
        simp
      exact h (singularSimplexEquiv X n σ) h4
    · exact allSmall_single
  rw [h3]

/-- The subgroup of 𝒰-small chains (Finsupp side). -/
def smallChainsSubgroup (n : ℕ) : AddSubgroup (SingularChain ℤ X n) :=
  { carrier := {c | AllSmall 𝒰 c}
    zero_mem' := allSmall_zero
    add_mem' := fun ha hb => allSmall_add ha hb
    neg_mem' := fun ha => allSmall_neg ha }

/-- Reverse direction: if x is 𝒰-small, then it is in the image of the small inclusion. -/
theorem isSmall_imp_small_chain_image (n : ℕ)
    (x : ((singularSSet X).chainComplex ZGrp).X n)
    (hx : isSmall_mlib 𝒰 n x) :
    x ∈ Set.range ((smallChainInclusion_cover 𝒰).f n) := by
  let c := (mathlibToFinsupp X n).hom x
  have hc : AllSmall 𝒰 c := hx
  let L_chain := (singularSSet X).chainComplex ZGrp
  let K_chain := smallChainComplex_cover 𝒰
  let i_chain : K_chain ⟶ L_chain := smallChainInclusion_cover 𝒰
  have h_main : ∀ (d : SingularChain ℤ X n), AllSmall 𝒰 d →
      (finsuppToMathlib X n).hom d ∈ Set.range (i_chain.f n) := by
    classical
    let P : SingularChain ℤ X n → Prop := fun d =>
      AllSmall 𝒰 d → (finsuppToMathlib X n).hom d ∈ Set.range (i_chain.f n)
    have h_ind : ∀ (d : SingularChain ℤ X n), P d := by
      intro d
      induction d using Finsupp.induction with
      | zero =>
        intro _
        have h0 : (i_chain.f n).hom (0 : K_chain.X n) = (0 : L_chain.X n) := by
          exact map_zero (i_chain.f n).hom
        exact ⟨(0 : K_chain.X n), h0⟩
      | single_add σ z d hσ hz ih =>
        intro h_all
        have hσ_small : IsSmallWithRespectTo 𝒰 σ := by
          have h1 : (Finsupp.single σ z + d) σ ≠ 0 := by
            have h_dσ : d σ = 0 := by
              simpa [Finsupp.mem_support_iff] using hσ
            have h : (Finsupp.single σ z + d) σ = z := by
              rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl, h_dσ] ; ring
            rw [h] ; exact hz
          have h2 : σ ∈ Finsupp.support (Finsupp.single σ z + d) := by
            rw [Finsupp.mem_support_iff] ; exact h1
          exact h_all σ h2
        let σ' : (singularSSet X) _⦋n⦌ := (singularSimplexEquiv X n).symm σ
        have hσ'_small : isSmallSimplex_cover 𝒰 σ' :=
          (isSmallSimplex_iff_IsSmallWithRespectTo 𝒰 σ').mpr hσ_small
        let σ_small : smallSSet_cover 𝒰 _⦋n⦌ := ⟨σ', hσ'_small⟩
        let g_small : K_chain.X n :=
          (smallSSet_cover 𝒰).ιChainComplex (R := ZGrp) σ_small (1 : ℤ)
        have h_small_elem : (finsuppToMathlib X n).hom (Finsupp.single σ z) =
            z • (i_chain.f n).hom g_small := by
          have h_eq1 : Finsupp.single σ z = z • Finsupp.single σ (1 : ℤ) := by
            simp [Finsupp.smul_single]
          rw [h_eq1]
          have h : (finsuppToMathlib X n).hom (z • Finsupp.single σ (1 : ℤ)) =
              z • (finsuppToMathlib X n).hom (Finsupp.single σ (1 : ℤ)) :=
            map_zsmul (finsuppToMathlib X n).hom _ _
          rw [h]
          rw [finsuppToMathlib_single]
          have h4 : (singularSSet X).ιChainComplex (R := ZGrp) σ' (1 : ℤ) =
              (i_chain.f n).hom g_small := by
            have h5 := smallChainInclusion_cover_ι 𝒰 n σ_small
            exact congr_arg (fun f : ZGrp ⟶ _ => f (1 : ℤ)) h5.symm
          rw [h4]
        have h_d_small : AllSmall 𝒰 d := by
          intro τ hτ
          have h_dτ : d τ ≠ 0 := by simpa [Finsupp.mem_support_iff] using hτ
          have h_ne : τ ≠ σ := by
            intro h_eq
            rw [h_eq] at hτ
            exact hσ hτ
          have hτ' : (Finsupp.single σ z + d) τ ≠ 0 := by
            have h1 : (Finsupp.single σ z + d) τ = (Finsupp.single σ z) τ + d τ := by
              exact Finsupp.add_apply (Finsupp.single σ z) d τ
            have h2 : (Finsupp.single σ z) τ = 0 := by
              apply Finsupp.single_eq_of_ne
              exact h_ne
            rw [h1, h2, zero_add]
            exact h_dτ
          exact h_all τ (by rwa [Finsupp.mem_support_iff])
        rcases ih h_d_small with ⟨y', hy'⟩
        let y_sum : K_chain.X n := z • g_small + y'
        have h5 : (i_chain.f n).hom y_sum =
            z • (i_chain.f n).hom g_small + (i_chain.f n).hom y' := by
          have h_add : (i_chain.f n).hom (z • g_small + y') =
              (i_chain.f n).hom (z • g_small) + (i_chain.f n).hom y' :=
            map_add (i_chain.f n).hom _ _
          have h_zsmul : (i_chain.f n).hom (z • g_small) =
              z • (i_chain.f n).hom g_small :=
            map_zsmul (i_chain.f n).hom _ _
          rw [h_add, h_zsmul]
        have h6 : (finsuppToMathlib X n).hom (Finsupp.single σ z + d) =
            z • (i_chain.f n).hom g_small + (finsuppToMathlib X n).hom d := by
          have h_add : (finsuppToMathlib X n).hom (Finsupp.single σ z + d) =
              (finsuppToMathlib X n).hom (Finsupp.single σ z) +
              (finsuppToMathlib X n).hom d :=
            map_add (finsuppToMathlib X n).hom _ _
          rw [h_add, h_small_elem]
        refine ⟨y_sum, ?_⟩
        rw [h5, h6, hy']
    intro d hd
    exact h_ind d hd
  have h_main2 : (finsuppToMathlib X n).hom c ∈ Set.range (i_chain.f n) := h_main c hc
  have h_inv : (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom x) = x := by
    have h_rightInv : (mathlibToFinsupp X n ≫ finsuppToMathlib X n).hom x =
        (𝟙 ((singularSSet X).chainComplex ZGrp).X n).hom x := by
      rw [mathlibToFinsupp_rightInverse X n]
    have h_comp : (mathlibToFinsupp X n ≫ finsuppToMathlib X n).hom x =
        (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom x) := by
      simp
    have h_id : (𝟙 ((singularSSet X).chainComplex ZGrp).X n).hom x = x := by
      simp
    have h_goal : (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom x) = x := by
      calc
        (finsuppToMathlib X n).hom ((mathlibToFinsupp X n).hom x)
          = (mathlibToFinsupp X n ≫ finsuppToMathlib X n).hom x := h_comp.symm
        _ = (𝟙 ((singularSSet X).chainComplex ZGrp).X n).hom x := h_rightInv
        _ = x := h_id
    exact h_goal
  rw [h_inv] at h_main2
  exact h_main2

/-- Forward direction: if x is in the image of the small inclusion, then it is 𝒰-small. -/
theorem small_chain_image_imp_isSmall (n : ℕ)
    (x : ((singularSSet X).chainComplex ZGrp).X n)
    (hx : x ∈ Set.range ((smallChainInclusion_cover 𝒰).f n)) :
    isSmall_mlib 𝒰 n x := by
  rcases hx with ⟨y, rfl⟩
  let S := smallSSet_cover 𝒰
  let H := AddCommGrpCat.of (smallChainsSubgroup 𝒰 n)
  let incl : H ⟶ AddCommGrpCat.of (SingularChain ℤ X n) :=
    AddCommGrpCat.ofHom (smallChainsSubgroup 𝒰 n).subtype
  let g : S _⦋n⦌ → (ZGrp ⟶ H) := fun x_small =>
    AddCommGrpCat.ofHom
      { toFun := fun z : ℤ =>
          ⟨z • Finsupp.single (singularSimplexEquiv X n (smallι_cover 𝒰 |>.app _ x_small)) (1 : ℤ),
            allSmall_smul (allSmall_single
              ((isSmallSimplex_iff_IsSmallWithRespectTo 𝒰 (smallι_cover 𝒰 |>.app _ x_small)).mp x_small.prop))⟩
        map_zero' := by
          apply Subtype.ext
          simp
        map_add' := by
          intro a b
          apply Subtype.ext
          simp [add_smul]  }
  let cocone := Cofan.mk H g
  let φ : (S.chainComplex ZGrp).X n ⟶ H :=
    (S.isColimitChainComplexXCofan ZGrp n).desc cocone
  have h_comm : (smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n = φ ≫ incl := by
    apply (S.isColimitChainComplexXCofan ZGrp n).hom_ext
    intro i
    let x_small : S _⦋n⦌ := i.as
    have h_ι_eq : (S.chainComplexXCofan ZGrp n).ι.app i = S.ιChainComplex (R := ZGrp) x_small := by rfl
    have h_fac1 : S.ιChainComplex (R := ZGrp) x_small ≫ (smallChainInclusion_cover 𝒰).f n =
        (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) :=
      smallChainInclusion_cover_ι 𝒰 n x_small
    have h_fac2 : S.ιChainComplex (R := ZGrp) x_small ≫ φ = g x_small := by
      exact (S.isColimitChainComplexXCofan ZGrp n).fac cocone (Discrete.mk x_small)
    have h_left : S.ιChainComplex (R := ZGrp) x_small ≫ ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n) =
        (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n := by
      calc
        S.ιChainComplex (R := ZGrp) x_small ≫ ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n)
          = (S.ιChainComplex (R := ZGrp) x_small ≫ (smallChainInclusion_cover 𝒰).f n) ≫ mathlibToFinsupp X n := by
            rw [Category.assoc]
        _ = ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small)) ≫ mathlibToFinsupp X n := by
            exact congr_arg (fun f : ZGrp ⟶ _ => f ≫ mathlibToFinsupp X n) h_fac1
    have h_mid : (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n =
        g x_small ≫ incl := by
      let σ_simp := singularSimplexEquiv X n (smallι_cover 𝒰 |>.app _ x_small)
      have h1 : ∀ (z : ℤ),
          ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n).hom z =
          z • Finsupp.single σ_simp (1 : ℤ) := by
        intro z
        have h21 : ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n).hom z =
            (mathlibToFinsupp X n).hom (((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small)) z) := by
          rfl
        rw [h21]
        have h_map_zsmul : ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small)) z =
            z • ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small)) (1 : ℤ) := by
          have h : ∀ (f : ZGrp ⟶ ((singularSSet X).chainComplex ZGrp).X n) (z : ℤ),
              f.hom z = z • f.hom (1 : ℤ) := by
            intro f z
            simpa [ZGrp] using map_zsmul f.hom z (1 : ℤ)
          exact h _ z
        rw [h_map_zsmul]
        rw [map_zsmul (mathlibToFinsupp X n).hom]
        rw [mathlibToFinsupp_ι]
      have h2 : ∀ (z : ℤ), (g x_small ≫ incl).hom z = z • Finsupp.single σ_simp (1 : ℤ) := by
        intro z
        rfl
      have h : ∀ (z : ℤ),
          ((singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n).hom z =
          (g x_small ≫ incl).hom z := by
        intro z
        rw [h1 z, h2 z]
      apply AddCommGrpCat.ext
      intro z
      exact h z
    have h_right : g x_small ≫ incl = S.ιChainComplex (R := ZGrp) x_small ≫ (φ ≫ incl) := by
      calc
        g x_small ≫ incl
          = (S.ιChainComplex (R := ZGrp) x_small ≫ φ) ≫ incl := by rw [h_fac2]
        _ = S.ιChainComplex (R := ZGrp) x_small ≫ (φ ≫ incl) := by rw [Category.assoc]
    have h_goal : S.ιChainComplex (R := ZGrp) x_small ≫ ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n) =
        S.ιChainComplex (R := ZGrp) x_small ≫ (φ ≫ incl) := by
      calc
        S.ιChainComplex (R := ZGrp) x_small ≫ ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n)
          = (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) ≫ mathlibToFinsupp X n := h_left
        _ = g x_small ≫ incl := h_mid
        _ = S.ιChainComplex (R := ZGrp) x_small ≫ (φ ≫ incl) := h_right
    rw [h_ι_eq]
    exact h_goal
  have h4 : ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n).hom y =
      (φ ≫ incl).hom y := by
    have h41 : ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n) = (φ ≫ incl) := h_comm
    exact congr_arg (fun (f : (smallChainComplex_cover 𝒰).X n ⟶ AddCommGrpCat.of (SingularChain ℤ X n)) => f.hom y) h41
  have h5 : (mathlibToFinsupp X n).hom (((smallChainInclusion_cover 𝒰).f n).hom y) =
      incl.hom (φ.hom y) := by
    calc
      (mathlibToFinsupp X n).hom (((smallChainInclusion_cover 𝒰).f n).hom y)
        = ((smallChainInclusion_cover 𝒰).f n ≫ mathlibToFinsupp X n).hom y := by rfl
      _ = (φ ≫ incl).hom y := h4
      _ = incl.hom (φ.hom y) := by rfl
  have h_goal : isSmall_mlib 𝒰 n (((smallChainInclusion_cover 𝒰).f n).hom y) := by
    dsimp only [isSmall_mlib]
    have h9 : (mathlibToFinsupp X n).hom (((smallChainInclusion_cover 𝒰).f n).hom y) = incl.hom (φ.hom y) := h5
    rw [h9]
    have h10 : incl.hom (φ.hom y) ∈ smallChainsSubgroup 𝒰 n := (φ.hom y).property
    simpa [smallChainsSubgroup] using h10
  exact h_goal

/-- Full equivalence: x is 𝒰-small iff it is in the image of the small chain inclusion. -/
theorem isSmall_iff_in_small_chain_image (n : ℕ)
    (x : ((singularSSet X).chainComplex ZGrp).X n) :
    isSmall_mlib 𝒰 n x ↔ x ∈ Set.range ((smallChainInclusion_cover 𝒰).f n) := by
  constructor
  · exact isSmall_imp_small_chain_image 𝒰 n x
  · exact small_chain_image_imp_isSmall 𝒰 n x

/-- The inclusion of small chains is injective at each degree. -/
lemma smallChainInclusion_injective (n : ℕ) :
    Function.Injective ((smallChainInclusion_cover 𝒰).f n).hom := by
  let L_chain := (singularSSet X).chainComplex ZGrp
  let K_chain := smallChainComplex_cover 𝒰
  let i_chain : K_chain ⟶ L_chain := smallChainInclusion_cover 𝒰
  let S := smallSSet_cover 𝒰
  classical
  let g : (singularSSet X) _⦋n⦌ → (ZGrp ⟶ K_chain.X n) :=
    fun σ => if h : isSmallSimplex_cover 𝒰 σ then
      S.ιChainComplex (R := ZGrp) (⟨σ, h⟩ : S _⦋n⦌)
    else 0
  let cocone := Cofan.mk (K_chain.X n) g
  let r : L_chain.X n ⟶ K_chain.X n :=
    ((singularSSet X).isColimitChainComplexXCofan ZGrp n).desc cocone
  have h_fac_formula : ∀ (σ : (singularSSet X) _⦋n⦌),
      (singularSSet X).ιChainComplex (R := ZGrp) σ ≫ r = g σ := by
    intro σ
    exact (singularSSet X).isColimitChainComplexXCofan ZGrp n |>.fac cocone (Discrete.mk σ)
  have h_retract : i_chain.f n ≫ r = 𝟙 (K_chain.X n) := by
    apply (S.isColimitChainComplexXCofan ZGrp n).hom_ext
    intro i
    let x_small : S _⦋n⦌ := i.as
    have h_small : isSmallSimplex_cover 𝒰 (smallι_cover 𝒰 |>.app _ x_small) := x_small.prop
    have h1 : S.ιChainComplex (R := ZGrp) x_small ≫ i_chain.f n =
        (singularSSet X).ιChainComplex (R := ZGrp) (smallι_cover 𝒰 |>.app _ x_small) :=
      smallChainInclusion_cover_ι 𝒰 n x_small
    let σ_small : (singularSSet X) _⦋n⦌ := smallι_cover 𝒰 |>.app _ x_small
    have h_fac : (singularSSet X).ιChainComplex (R := ZGrp) σ_small ≫ r =
        S.ιChainComplex (R := ZGrp) (⟨σ_small, h_small⟩ : S _⦋n⦌) := by
      have h : (singularSSet X).ιChainComplex (R := ZGrp) σ_small ≫ r = g σ_small :=
        h_fac_formula σ_small
      rw [h]
      dsimp only [g]
      rw [dif_pos h_small]
    have h_eq : S.ιChainComplex (R := ZGrp) (⟨σ_small, h_small⟩ : S _⦋n⦌) =
        S.ιChainComplex (R := ZGrp) x_small := by
      congr
    have h2 : S.ιChainComplex (R := ZGrp) x_small ≫ i_chain.f n ≫ r =
        S.ιChainComplex (R := ZGrp) x_small := by
      calc
        S.ιChainComplex (R := ZGrp) x_small ≫ i_chain.f n ≫ r
          = (S.ιChainComplex (R := ZGrp) x_small ≫ i_chain.f n) ≫ r := by
            rw [Category.assoc]
        _ = (singularSSet X).ιChainComplex (R := ZGrp) σ_small ≫ r := by rw [h1]
        _ = S.ιChainComplex (R := ZGrp) (⟨σ_small, h_small⟩ : S _⦋n⦌) := h_fac
        _ = S.ιChainComplex (R := ZGrp) x_small := h_eq
    have h_id : S.ιChainComplex (R := ZGrp) x_small ≫ 𝟙 (K_chain.X n) =
        S.ιChainComplex (R := ZGrp) x_small := by
      exact Category.comp_id (S.ιChainComplex x_small)
    have h_goal : S.ιChainComplex (R := ZGrp) x_small ≫ i_chain.f n ≫ r =
        S.ιChainComplex (R := ZGrp) x_small ≫ 𝟙 (K_chain.X n) := by
      rw [h2, h_id]
    exact h_goal
  intro y₁ y₂ h
  have h_eq1 : r.hom ((i_chain.f n).hom y₁) = r.hom ((i_chain.f n).hom y₂) := by
    rw [h]
  have h4 : (i_chain.f n ≫ r).hom y₁ = (i_chain.f n ≫ r).hom y₂ := by
    have h6 : (i_chain.f n ≫ r).hom y₁ = r.hom ((i_chain.f n).hom y₁) := by rfl
    have h7 : (i_chain.f n ≫ r).hom y₂ = r.hom ((i_chain.f n).hom y₂) := by rfl
    rw [h6, h7]
    exact h_eq1
  have h8 : y₁ = y₂ := by
    have h91 : (i_chain.f n ≫ r).hom y₁ = y₁ := by
      have h_eq : i_chain.f n ≫ r = 𝟙 (K_chain.X n) := h_retract
      rw [h_eq]
      ; simp
    have h92 : (i_chain.f n ≫ r).hom y₂ = y₂ := by
      have h_eq : i_chain.f n ≫ r = 𝟙 (K_chain.X n) := h_retract
      rw [h_eq]
      ; simp
    have h11 : y₁ = y₂ := by
      rw [←h91, ←h92]
      exact h4
    exact h11
  exact h8

/-!
### Full small chain theorem (IsIso version)
-/

/-- Surjectivity on homology for the small chain inclusion. -/
theorem smallChainInclusion_surjectivity (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) (n : ℕ)
    (z : ((singularSSet X).chainComplex ZGrp).X (n + 1))
    (hz_cycle : (((singularSSet X).chainComplex ZGrp).d (n + 1) n).hom z = 0) :
    ∃ (y : (smallChainComplex_cover 𝒰).X (n + 1)),
      ((smallChainComplex_cover 𝒰).d (n + 1) n).hom y = 0 ∧
      ∃ (c : ((singularSSet X).chainComplex ZGrp).X (n + 2)),
        (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom c =
          z - ((smallChainInclusion_cover 𝒰).f (n + 1)).hom y := by
  let L_chain := (singularSSet X).chainComplex ZGrp
  let K_chain := smallChainComplex_cover 𝒰
  let i_chain : K_chain ⟶ L_chain := smallChainInclusion_cover 𝒰
  have h1 := concrete_smallChain_surjectivity 𝒰 hU hcover n z hz_cycle
  rcases h1 with ⟨y_full, hy_small, hy_cycle, c, hc⟩
  have h2 : y_full ∈ Set.range (i_chain.f (n + 1)) :=
    (isSmall_iff_in_small_chain_image 𝒰 (n + 1) y_full).mp hy_small
  rcases h2 with ⟨y, hy_eq⟩
  refine ⟨y, ?_, c, ?_⟩
  · -- Show y is a cycle
    have h3 : (L_chain.d (n + 1) n).hom ((i_chain.f (n + 1)).hom y) = 0 := by
      rw [hy_eq] ; exact hy_cycle
    have h_comm : K_chain.d (n + 1) n ≫ i_chain.f n =
        i_chain.f (n + 1) ≫ L_chain.d (n + 1) n :=
      (i_chain.comm (n + 1) n).symm
    have h5 : (K_chain.d (n + 1) n ≫ i_chain.f n).hom y = 0 := by
      calc
        (K_chain.d (n + 1) n ≫ i_chain.f n).hom y
          = (i_chain.f (n + 1) ≫ L_chain.d (n + 1) n).hom y := by rw [h_comm]
        _ = (L_chain.d (n + 1) n).hom ((i_chain.f (n + 1)).hom y) := by rfl
        _ = 0 := h3
    have h7 : (i_chain.f n).hom ((K_chain.d (n + 1) n).hom y) =
        (i_chain.f n).hom (0 : K_chain.X n) := by
      have h8 : (K_chain.d (n + 1) n ≫ i_chain.f n).hom y =
          (i_chain.f n).hom ((K_chain.d (n + 1) n).hom y) := by rfl
      have h9 : (i_chain.f n).hom (0 : K_chain.X n) = 0 := map_zero _
      have h10 : (i_chain.f n).hom ((K_chain.d (n + 1) n).hom y) = 0 := by
        rw [←h8]
        exact h5
      rw [h9]
      exact h10
    have h_inj : Function.Injective (i_chain.f n).hom :=
      smallChainInclusion_injective 𝒰 n
    exact h_inj h7
  · -- Show z - ι(y) = d(c)
    have h9 : z - (i_chain.f (n + 1)).hom y = z - y_full := by
      rw [hy_eq]
    rw [h9]
    exact hc

/-- Injectivity on homology for the small chain inclusion. -/
theorem smallChainInclusion_injectivity' (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) (n : ℕ)
    (y : (smallChainComplex_cover 𝒰).X (n + 1))
    (hy_cycle : ((smallChainComplex_cover 𝒰).d (n + 1) n).hom y = 0)
    (b : ((singularSSet X).chainComplex ZGrp).X (n + 2))
    (hb : (((singularSSet X).chainComplex ZGrp).d (n + 2) (n + 1)).hom b =
        ((smallChainInclusion_cover 𝒰).f (n + 1)).hom y) :
    ∃ (c : (smallChainComplex_cover 𝒰).X (n + 2)),
      ((smallChainComplex_cover 𝒰).d (n + 2) (n + 1)).hom c = y := by
  let L_chain := (singularSSet X).chainComplex ZGrp
  let K_chain := smallChainComplex_cover 𝒰
  let i_chain : K_chain ⟶ L_chain := smallChainInclusion_cover 𝒰
  let y_full : L_chain.X (n + 1) := (i_chain.f (n + 1)).hom y
  have hy_small : isSmall_mlib 𝒰 (n + 1) y_full :=
    small_chain_image_imp_isSmall 𝒰 (n + 1) y_full ⟨y, rfl⟩
  have hy_full_cycle : (L_chain.d (n + 1) n).hom y_full = 0 := by
    have h_comm : K_chain.d (n + 1) n ≫ i_chain.f n =
        i_chain.f (n + 1) ≫ L_chain.d (n + 1) n :=
      (i_chain.comm (n + 1) n).symm
    have h5 : (K_chain.d (n + 1) n ≫ i_chain.f n).hom y =
        (L_chain.d (n + 1) n).hom y_full := by
      calc
        (K_chain.d (n + 1) n ≫ i_chain.f n).hom y
          = (i_chain.f (n + 1) ≫ L_chain.d (n + 1) n).hom y := by rw [h_comm]
        _ = (L_chain.d (n + 1) n).hom y_full := by rfl
    have h6 : (K_chain.d (n + 1) n ≫ i_chain.f n).hom y = 0 := by
      have h7 : (K_chain.d (n + 1) n ≫ i_chain.f n).hom y =
          (i_chain.f n).hom ((K_chain.d (n + 1) n).hom y) := by rfl
      rw [h7, hy_cycle]
      ; simp
    rw [h5] at h6
    exact h6
  have h1 := concrete_smallChain_injectivity 𝒰 hU hcover n y_full hy_small b hb
  rcases h1 with ⟨c_full, hc_small, hc_eq⟩
  have h2 : c_full ∈ Set.range (i_chain.f (n + 2)) :=
    (isSmall_iff_in_small_chain_image 𝒰 (n + 2) c_full).mp hc_small
  rcases h2 with ⟨c, hc_eq2⟩
  refine ⟨c, ?_⟩
  have h3 : (L_chain.d (n + 2) (n + 1)).hom ((i_chain.f (n + 2)).hom c) =
      (i_chain.f (n + 1)).hom y := by
    rw [hc_eq2] ; exact hc_eq
  have h_comm2 : K_chain.d (n + 2) (n + 1) ≫ i_chain.f (n + 1) =
      i_chain.f (n + 2) ≫ L_chain.d (n + 2) (n + 1) :=
    (i_chain.comm (n + 2) (n + 1)).symm
  have h4 : (K_chain.d (n + 2) (n + 1) ≫ i_chain.f (n + 1)).hom c =
      (L_chain.d (n + 2) (n + 1)).hom ((i_chain.f (n + 2)).hom c) := by
    calc
      (K_chain.d (n + 2) (n + 1) ≫ i_chain.f (n + 1)).hom c
        = (i_chain.f (n + 2) ≫ L_chain.d (n + 2) (n + 1)).hom c := by rw [h_comm2]
      _ = (L_chain.d (n + 2) (n + 1)).hom ((i_chain.f (n + 2)).hom c) := by rfl
  have h5 : (i_chain.f (n + 1)).hom ((K_chain.d (n + 2) (n + 1)).hom c) =
      (i_chain.f (n + 1)).hom y := by
    have h6 : (K_chain.d (n + 2) (n + 1) ≫ i_chain.f (n + 1)).hom c =
        (i_chain.f (n + 1)).hom ((K_chain.d (n + 2) (n + 1)).hom c) := by rfl
    have h7 : (K_chain.d (n + 2) (n + 1) ≫ i_chain.f (n + 1)).hom c =
        (L_chain.d (n + 2) (n + 1)).hom ((i_chain.f (n + 2)).hom c) := h4
    have h8 : (L_chain.d (n + 2) (n + 1)).hom ((i_chain.f (n + 2)).hom c) =
        (i_chain.f (n + 1)).hom y := h3
    rw [←h6, h7, h8]
  have h_inj : Function.Injective (i_chain.f (n + 1)).hom :=
    smallChainInclusion_injective 𝒰 (n + 1)
  exact h_inj h5

/-- **Full small chain theorem:** the inclusion of small chains into full chains
    induces an isomorphism on homology in all degrees ≥ 1. -/
theorem smallChainTheorem_cover (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) :
    ∀ (n : ℕ), IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) (n + 1)) := by
  intro n
  let C_small := smallChainComplex_cover 𝒰
  let C_full := (singularSSet X).chainComplex ZGrp
  let f : C_small ⟶ C_full := smallChainInclusion_cover 𝒰
  let i := n + 2
  let j := n + 1
  let k := n
  let c := ComplexShape.down ℕ
  have h_rel_prev : c.Rel i j := by
    have h : j + 1 = i := by omega
    exact ComplexShape.down_mk i j h
  have h_rel_next : c.Rel j k := by
    have h : k + 1 = j := by omega
    exact ComplexShape.down_mk j k h
  have hi : c.prev j = i := by exact ComplexShape.prev_eq' c h_rel_prev
  have hk : c.next j = k := by
    exact c.next_eq' h_rel_next
  let S₁ : ShortComplex AddCommGrpCat := C_small.sc' i j k
  let S₂ : ShortComplex AddCommGrpCat := C_full.sc' i j k
  let φ : S₁ ⟶ S₂ :=
    (HomologicalComplex.shortComplexFunctor' AddCommGrpCat c i j k).map f
  have h_surj : ∀ (z : S₂.X₂), S₂.g.hom z = 0 →
      ∃ (y : S₁.X₂), S₁.g.hom y = 0 ∧
        ∃ (c : S₂.X₁), S₂.f.hom c = z - φ.τ₂.hom y := by
    intro z hz
    have hz' : (C_full.d j k).hom z = 0 := hz
    have h_main := smallChainInclusion_surjectivity 𝒰 hU hcover n z hz'
    rcases h_main with ⟨y, hy_cycle, c, hc⟩
    refine ⟨y, hy_cycle, c, ?_⟩
    exact hc
  have h_inj : ∀ (y : S₁.X₂), S₁.g.hom y = 0 →
      (∃ (b : S₂.X₁), S₂.f.hom b = φ.τ₂.hom y) →
      ∃ (c : S₁.X₁), S₁.f.hom c = y := by
    intro y hy hb
    have hy' : (C_small.d j k).hom y = 0 := hy
    rcases hb with ⟨b, hb_eq⟩
    have h_main := smallChainInclusion_injectivity' 𝒰 hU hcover n y hy' b hb_eq
    rcases h_main with ⟨c, hc⟩
    exact ⟨c, hc⟩
  have h_main1 : IsIso (ShortComplex.homologyMap φ) :=
    shortComplex_quasiIso_of_elementwise φ h_surj h_inj
  have h_main2 : ShortComplex.QuasiIso φ := by
    rw [ShortComplex.quasiIso_iff]
    exact h_main1
  let e : (HomologicalComplex.shortComplexFunctor AddCommGrpCat c j) ≅
      (HomologicalComplex.shortComplexFunctor' AddCommGrpCat c i j k) :=
    HomologicalComplex.natIsoSc' AddCommGrpCat c i j k hi hk
  let φ_sc : C_small.sc j ⟶ C_full.sc j :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat c j).map f
  have h_nat : φ_sc ≫ (e.app C_full).hom = (e.app C_small).hom ≫ φ := by
    exact e.hom.naturality f
  have h_main3 : ShortComplex.QuasiIso φ_sc := by
    have h_iff : ShortComplex.QuasiIso φ_sc ↔ ShortComplex.QuasiIso φ :=
      ShortComplex.quasiIso_iff_of_arrow_mk_iso φ_sc φ
        (Arrow.isoOfNatIso e (Arrow.mk f))
    exact h_iff.mpr h_main2
  have h_main4 : IsIso (ShortComplex.homologyMap φ_sc) := by
    rw [ShortComplex.quasiIso_iff] at h_main3
    exact h_main3
  have h_main5 : IsIso (HomologicalComplex.homologyMap f j) := by
    have h_def : HomologicalComplex.homologyMap f j = ShortComplex.homologyMap φ_sc := by
      rfl
    rw [h_def]
    exact h_main4
  exact h_main5

/-- Auxiliary: every 0-boundary in the full complex comes from a small 1-chain. -/
lemma zero_boundary_lifts_to_small (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i)
    (b : ((singularSSet X).chainComplex ZGrp).X 1) :
    ∃ (d' : ((singularSSet X).chainComplex ZGrp).X 1),
      isSmall_mlib 𝒰 1 d' ∧
      (((singularSSet X).chainComplex ZGrp).d 1 0).hom d' =
      (((singularSSet X).chainComplex ZGrp).d 1 0).hom b := by
  have h_eventually : ∃ k : ℕ, isSmall_mlib 𝒰 1 ((sd_mathlib_iter X k 1).hom b) :=
    eventually_small_full 𝒰 hU hcover 1 b
  rcases h_eventually with ⟨k, hk_small⟩
  let sd_k_b := (sd_mathlib_iter X k 1).hom b
  let db := (((singularSSet X).chainComplex ZGrp).d 1 0).hom b
  let T_k_db := (T_mathlib_iter X k 0).hom db
  let d' := sd_k_b - T_k_db
  have h1 : isSmall_mlib 𝒰 1 sd_k_b := hk_small
  have hdb_small : isSmall_mlib 𝒰 0 db := by
    dsimp only [isSmall_mlib]
    exact allSmall_zero_dim 𝒰 hcover ((mathlibToFinsupp X 0).hom db)
  have h2 : isSmall_mlib 𝒰 1 T_k_db :=
    T_iter_preserves_small_mlib 𝒰 k 0 hdb_small
  have hd'_small : isSmall_mlib 𝒰 1 d' := by
    have h_neg : isSmall_mlib 𝒰 1 (-T_k_db) := isSmall_mlib_neg 𝒰 1 h2
    have h_add : isSmall_mlib 𝒰 1 (sd_k_b + (-T_k_db)) := isSmall_mlib_add 𝒰 1 h1 h_neg
    have h_eq : sd_k_b + (-T_k_db) = d' := by
      dsimp only [d'] ; abel
    rw [h_eq] at h_add
    exact h_add
  have h_eq_main : (((singularSSet X).chainComplex ZGrp).d 1 0).hom d' = db := by
    dsimp only [d']
    let C_full := (singularSSet X).chainComplex ZGrp
    let d21 := C_full.d 2 1
    let d10 := C_full.d 1 0
    let T_k1 := T_mathlib_iter X k 1
    let T_k0 := T_mathlib_iter X k 0
    let sd_k1 := sd_mathlib_iter X k 1
    have h_hom : T_k1 ≫ d21 + d10 ≫ T_k0 = sd_k1 - 𝟙 _ :=
      sd_mathlib_iter_homotopy X k 0
    have h_apply : (T_k1 ≫ d21 + d10 ≫ T_k0).hom b = (sd_k1 - 𝟙 _).hom b := by
      rw [h_hom]
    have h_eq1 : d21.hom (T_k1.hom b) + T_k0.hom (d10.hom b) = sd_k1.hom b - b := by
      have h1 : (T_k1 ≫ d21 + d10 ≫ T_k0).hom b =
          d21.hom (T_k1.hom b) + T_k0.hom (d10.hom b) := by
        rw [hom_add_apply] ; simp
      have h2 : (sd_k1 - 𝟙 _).hom b = sd_k1.hom b - b := by
        rw [hom_sub_apply] ; simp
      rw [h1, h2] at h_apply
      exact h_apply
    have h_eq2 : d10.hom (d21.hom (T_k1.hom b)) + d10.hom (T_k0.hom (d10.hom b)) =
        d10.hom (sd_k1.hom b) - d10.hom b := by
      have h : d10.hom (d21.hom (T_k1.hom b) + T_k0.hom (d10.hom b)) =
          d10.hom (sd_k1.hom b - b) := by rw [h_eq1]
      simpa [map_add, map_sub] using h
    have h_dd : d10.hom (d21.hom (T_k1.hom b)) = 0 := by
      have h : d21 ≫ d10 = 0 := by
        exact HomologicalComplex.d_comp_d C_full 2 1 0
      have h' : (d21 ≫ d10).hom (T_k1.hom b) = 0 := by
        rw [h] ; simp
      simpa [AddCommGrpCat.comp_apply] using h'
    rw [h_dd, zero_add] at h_eq2
    have h_final : d10.hom (T_k0.hom db) = d10.hom (sd_k1.hom b) - d10.hom b := h_eq2
    have h_sub : d10.hom (sd_k1.hom b - T_k0.hom db) =
        d10.hom (sd_k1.hom b) - d10.hom (T_k0.hom db) := by
      rw [map_sub]
    rw [h_sub]
    rw [h_final] ; abel
  exact ⟨d', hd'_small, h_eq_main⟩

theorem smallChainTheorem_cover_degree0 (hU : ∀ i, IsOpen (𝒰 i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, 𝒰 i) :
    IsIso (HomologicalComplex.homologyMap (smallChainInclusion_cover 𝒰) 0) := by
  let C_small := smallChainComplex_cover 𝒰
  let C_full := (singularSSet X).chainComplex ZGrp
  let f : C_small ⟶ C_full := smallChainInclusion_cover 𝒰
  let cs := ComplexShape.down ℕ
  let S₁ : ShortComplex AddCommGrpCat := C_small.sc 0
  let S₂ : ShortComplex AddCommGrpCat := C_full.sc 0
  let φ : S₁ ⟶ S₂ :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat cs 0).map f
  have h_prev : cs.prev 0 = 1 := by
    have h_rel : cs.Rel 1 0 := by exact ComplexShape.down_mk 1 0 rfl
    exact ComplexShape.prev_eq' cs h_rel
  let e1 : S₂.X₁ ≅ C_full.X 1 := eqToIso (congr_arg C_full.X h_prev)
  let e1' : S₁.X₁ ≅ C_small.X 1 := eqToIso (congr_arg C_small.X h_prev)
  have h_f0_inj : Function.Injective (f.f 0).hom :=
    smallChainInclusion_injective 𝒰 0
  have h_f0_surj : Function.Surjective (f.f 0).hom := by
    intro z
    have h_small : isSmall_mlib 𝒰 0 z := by
      dsimp only [isSmall_mlib]
      exact allSmall_zero_dim 𝒰 hcover ((mathlibToFinsupp X 0).hom z)
    exact (isSmall_iff_in_small_chain_image 𝒰 0 z).mp h_small
  have h_S2f : S₂.f = e1.hom ≫ C_full.d 1 0 := by
    have h_f_def : S₂.f = C_full.d (cs.prev 0) 0 := by
      simp [S₂, HomologicalComplex.sc]
      ; rfl
    rw [h_f_def]
    have h : ∀ (i i' : ℕ) (h_eq : i = i'),
        C_full.d i 0 = eqToHom (congr_arg C_full.X h_eq) ≫ C_full.d i' 0 := by
      intro i i' h_eq
      subst h_eq
      simp [eqToHom]
    have h1 := h (cs.prev 0) 1 h_prev
    have h_e1_hom : e1.hom = eqToHom (congr_arg C_full.X h_prev) := by
      simp [e1, eqToIso] ; rfl
    rw [h_e1_hom]
    exact h1
  have h_S1f : S₁.f = e1'.hom ≫ C_small.d 1 0 := by
    have h_f_def : S₁.f = C_small.d (cs.prev 0) 0 := by
      simp [S₁, HomologicalComplex.sc]
      ; rfl
    rw [h_f_def]
    have h : ∀ (i i' : ℕ) (h_eq : i = i'),
        C_small.d i 0 = eqToHom (congr_arg C_small.X h_eq) ≫ C_small.d i' 0 := by
      intro i i' h_eq
      subst h_eq
      simp [eqToHom]
    have h1 := h (cs.prev 0) 1 h_prev
    have h_e1'_hom : e1'.hom = eqToHom (congr_arg C_small.X h_prev) := by
      simp [e1', eqToIso] ; rfl
    rw [h_e1'_hom]
    exact h1
  have h_surj : ∀ (z : S₂.X₂), S₂.g.hom z = 0 →
      ∃ (y : S₁.X₂), S₁.g.hom y = 0 ∧
        ∃ (c : S₂.X₁), S₂.f.hom c = z - φ.τ₂.hom y := by
    intro z hz
    rcases h_f0_surj z with ⟨y, hy_eq⟩
    have h_φτ2 : φ.τ₂.hom y = (f.f 0).hom y := by rfl
    have h_y_cycle : S₁.g.hom y = 0 := by
      have h1 : S₂.g.hom (φ.τ₂.hom y) = 0 := by
        rw [h_φτ2, hy_eq] ; exact hz
      exact AddMonoidHom.mem_ker.mp rfl
    refine ⟨y, h_y_cycle, 0, ?_⟩
    have h_goal : S₂.f.hom (0 : S₂.X₁) = z - φ.τ₂.hom y := by
      rw [map_zero, h_φτ2, hy_eq] ; abel
    exact h_goal
  have h_inj : ∀ (y : S₁.X₂), S₁.g.hom y = 0 →
      (∃ (b : S₂.X₁), S₂.f.hom b = φ.τ₂.hom y) →
      ∃ (c : S₁.X₁), S₁.f.hom c = y := by
    intro y _ hb
    rcases hb with ⟨b, hb_eq⟩
    let b_full : C_full.X 1 := e1.hom b
    have h1 : (S₂.f).hom b = (e1.hom ≫ C_full.d 1 0).hom b := h_S2f ▸ rfl
    have h2 : (e1.hom ≫ C_full.d 1 0).hom b = (C_full.d 1 0).hom b_full := by
      simp [b_full]
    have h_φτ2 : φ.τ₂.hom y = (f.f 0).hom y := by rfl
    have hb_full : (C_full.d 1 0).hom b_full = (f.f 0).hom y := by
      rw [←h2, ←h1, hb_eq, h_φτ2]
    have h_lift := zero_boundary_lifts_to_small 𝒰 hU hcover b_full
    rcases h_lift with ⟨d', hd'_small, h_d'_eq⟩
    have h_d'_in_image : d' ∈ Set.range (f.f 1).hom :=
      (isSmall_iff_in_small_chain_image 𝒰 1 d').mp hd'_small
    rcases h_d'_in_image with ⟨c', hc'_eq⟩
    have h_eq_comm : f.f 1 ≫ C_full.d 1 0 = C_small.d 1 0 ≫ f.f 0 := f.comm 1 0
    have h_comm : (C_full.d 1 0).hom ((f.f 1).hom c') = (f.f 0).hom ((C_small.d 1 0).hom c') := by
      have h : (f.f 1 ≫ C_full.d 1 0).hom c' = (C_small.d 1 0 ≫ f.f 0).hom c' := by
        rw [h_eq_comm]
      have h1 : (f.f 1 ≫ C_full.d 1 0).hom c' = (C_full.d 1 0).hom ((f.f 1).hom c') := by
        exact AddCommGrpCat.comp_apply (f.f 1) (C_full.d 1 0) c'
      have h2 : (C_small.d 1 0 ≫ f.f 0).hom c' = (f.f 0).hom ((C_small.d 1 0).hom c') := by
        exact AddCommGrpCat.comp_apply (C_small.d 1 0) (f.f 0) c'
      rw [h1, h2] at h
      exact h
    have h_eq3 : (f.f 0).hom ((C_small.d 1 0).hom c') = (f.f 0).hom y := by
      calc
        (f.f 0).hom ((C_small.d 1 0).hom c')
          = (C_full.d 1 0).hom ((f.f 1).hom c') := h_comm.symm
        _ = (C_full.d 1 0).hom d' := by rw [hc'_eq]
        _ = (C_full.d 1 0).hom b_full := h_d'_eq
        _ = (f.f 0).hom y := hb_full
    have h_eq4 : (C_small.d 1 0).hom c' = y := h_f0_inj h_eq3
    let c'' : S₁.X₁ := e1'.inv c'
    have h_e1'_inv_hom_id : e1'.inv ≫ e1'.hom = 𝟙 (C_small.X 1) := e1'.inv_hom_id
    have h_e1'_apply : e1'.hom c'' = c' := by
      have h : ∀ (x : C_small.X 1), (e1'.inv ≫ e1'.hom).hom x = x := by
        intro x
        rw [h_e1'_inv_hom_id]
        ; simp
      exact h c'
    have h6 : (S₁.f).hom c'' = (e1'.hom ≫ C_small.d 1 0).hom c'' := h_S1f ▸ rfl
    have h7 : (e1'.hom ≫ C_small.d 1 0).hom c'' = (C_small.d 1 0).hom (e1'.hom c'') := by
      simp
    have h5 : (S₁.f).hom c'' = y := by
      rw [h6, h7, h_e1'_apply, h_eq4]
    exact ⟨c'', h5⟩
  exact shortComplex_quasiIso_of_elementwise φ h_surj h_inj


end OpenCoverSmallSubcomplex


end AlgebraicTopology
