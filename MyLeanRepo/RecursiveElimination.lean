module

/-
# Recursive Elimination Lemma

Drafts the recursive schedule for the Expansion Theorem.

Given a uniform expansion lemma, iterates it n-1 times to eliminate all weights,
tracking:
- R_m = radius bound at stage m
- V_m = volume lower bound at stage m

Recurrence:
- N_m = uniform expansion lemma with d_max = 2*R_m, lam_min = V_m
- R_{m-1} = 2 * N_m * R_m^2
- V_{m-1} = V_m^2 / (2*m)

Dependencies:
- UniformExpansionLemma (harbor/bacon, in progress)
- iterated_containment_gen_explicit (flattening, TBD)
-/

public import MyLeanRepo.ExpansionLemma
public import MyLeanRepo.IterativeElimination
public import MyLeanRepo.ExpansionTheoremAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Metric Classical BigOperators
open scoped BigOperators Pointwise

namespace RecursiveElimination

/-- One step of the recursive elimination.
Given m weights, a set A with radius bound R and scaled sumset volume ≥ V,
apply the uniform expansion lemma to eliminate one weight.
Returns N, the eliminated index j, the new set A', and the new radius/volume bounds. -/
lemma one_step_elimination
    -- Uniform expansion lemma hypothesis (bounded factory)
    (h_expansion_uniform : ∀ (m : ℕ), 2 ≤ m → ∀ (d_max lam_min : ℝ),
      0 < d_max → 0 < lam_min →
      ∃ (N_max : ℕ), ∀ (A : Set ℝ), IsCompact A → A.Nonempty → diam A ≤ d_max →
        ∀ (v : Fin m → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
          ENNReal.ofReal lam_min ≤ volume (ExpansionLemma.scaledSumset v A) →
          ∃ (j : Fin m),
            volume (ExpansionLemma.scaledSumsetExcept v j
              (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N_max)) ≥
            ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A))
    {m : ℕ} (hm : 2 ≤ m)
    {R V : ℝ} (hR_pos : 0 < R) (hV_pos : 0 < V)
    {A : Set ℝ} (hA_compact : IsCompact A) (hA_nonempty : A.Nonempty)
    (hA_bdd : A ⊆ Set.Icc (-R) R)
    {v : Fin m → ℝ} (hv : ∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hvol : ENNReal.ofReal V ≤ volume (ExpansionLemma.scaledSumset v A)) :
    ∃ (N : ℕ) (j : Fin m),
      let A' := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N
      let R' := 2 * (N : ℝ) * R^2
      let V' := V^2 / (2 * (m : ℝ))
      IsCompact A' ∧ A'.Nonempty ∧ A' ⊆ Set.Icc (-R') R' ∧
      0 < V' ∧
      ENNReal.ofReal V' ≤ volume (ExpansionLemma.scaledSumsetExcept v j A') := by
  -- Get N_max from uniform expansion lemma
  have h_diam : diam A ≤ 2 * R := by
    have h1 : A ⊆ Set.Icc (-R) R := hA_bdd
    have h2 : Bornology.IsBounded (Set.Icc (-R) R) := isCompact_Icc.isBounded
    have h3 : diam A ≤ diam (Set.Icc (-R) R) := diam_mono h1 h2
    have h4 : diam (Set.Icc (-R) R) = 2 * R := by
      rw [Real.diam_Icc (by linarith)] <;> ring
    rw [h4] at h3
    exact h3
  rcases h_expansion_uniform m hm (2 * R) V (by positivity) hV_pos with ⟨N, hN⟩
  rcases hN A hA_compact hA_nonempty h_diam v hv hvol with ⟨j, hvol'⟩
  let A' := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N
  let R' := 2 * (N : ℝ) * R^2
  let V' := V^2 / (2 * (m : ℝ))
  refine ⟨N, j, ?_⟩
  have hA'_compact : IsCompact A' :=
    WeakTwoEndsSumProduct.iteratedDifference_compact
      (WeakTwoEndsSumProduct.productSet_compact hA_compact)
  have hPS_nonempty : (ExpansionLemma.productSet A 2).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    refine ⟨a * a, ?_⟩
    refine ⟨fun _ => a, fun _ => ha, ?_⟩
    rw [Fin.prod_univ_two] <;> simp
  have hA'_nonempty : A'.Nonempty := by
    have h_sum_nonempty : (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N).Nonempty := by
      have h_main : ∀ (k : ℕ), (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) k).Nonempty := by
        intro k
        induction k with
        | zero =>
          simp [ExpansionLemma.iteratedSumset]
          <;> exact ⟨0, by simp⟩
        | succ k ih =>
          rcases hPS_nonempty with ⟨s, hs⟩
          rcases ih with ⟨x, hx⟩
          exact ⟨s + x, ⟨s, hs, x, hx, rfl⟩⟩
      exact h_main N
    rcases h_sum_nonempty with ⟨x, hx⟩
    have h0 : (0 : ℝ) ∈ A' := by
      simp only [A', ExpansionLemma.iteratedDifference]
      exact ⟨x, hx, x, hx, by ring⟩
    exact ⟨0, h0⟩
  have hA'_bdd : A' ⊆ Set.Icc (-R') R' := by
    have hR_nonneg : 0 ≤ R := by linarith
    have h1 : ExpansionLemma.productSet A 2 ⊆ Set.Icc (-(R^2)) (R^2) := by
      intro z hz
      have h_exists : ∃ (a : Fin 2 → ℝ), (∀ i, a i ∈ A) ∧ z = ∏ i : Fin 2, a i := by
        simpa [ExpansionLemma.productSet] using hz
      rcases h_exists with ⟨a, ha, h_eq⟩
      have h3 : a 0 ∈ Set.Icc (-R) R := hA_bdd (ha 0)
      have h4 : a 1 ∈ Set.Icc (-R) R := hA_bdd (ha 1)
      have h5 : -R^2 ≤ a 0 * a 1 := by nlinarith [h3.1, h3.2, h4.1, h4.2]
      have h6 : a 0 * a 1 ≤ R^2 := by nlinarith [h3.1, h3.2, h4.1, h4.2]
      have h_prod : (∏ i : Fin 2, a i) = a 0 * a 1 := by simp [Fin.prod_univ_two] <;> ring
      rw [h_eq, h_prod]; exact ⟨h5, h6⟩
    have h2 : ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N ⊆
        Set.Icc (-(N : ℝ) * R^2) ((N : ℝ) * R^2) :=
      WeakTwoEndsSumProduct.iteratedSumset_bounded (N := N) (by positivity) h1
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hx' := h2 hx
    have hy' := h2 hy
    have h_z1 : -R' ≤ x - y := by dsimp only [R']; nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
    have h_z2 : x - y ≤ R' := by dsimp only [R']; nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
    exact ⟨h_z1, h_z2⟩
  have hV'_pos : 0 < V' := by
    dsimp only [V']
    apply div_pos
    · exact sq_pos_of_pos hV_pos
    · have h : 0 < (2 * (m : ℝ)) := by positivity
      exact h
  -- Volume bound: diam(A) ≥ V / (2*m), so diam(A) * V ≥ V^2 / (2*m)
  have h_diam_lower : ENNReal.ofReal (V / (2 * (m : ℝ))) ≤ ENNReal.ofReal (diam A) :=
    WeakTwoEndsSumProduct.diam_lower_from_scaledSumset_volume hA_nonempty hA_compact.isBounded hv hvol hV_pos (by linarith)
  have h_vol_new : ENNReal.ofReal V' ≤ volume (ExpansionLemma.scaledSumsetExcept v j A') := by
    dsimp only [V']
    have h1 : ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) ≤
        volume (ExpansionLemma.scaledSumsetExcept v j A') := hvol'
    have h2 : ENNReal.ofReal (V^2 / (2 * (m : ℝ))) ≤
        ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) := by
      have h3 : ENNReal.ofReal (V / (2 * (m : ℝ))) ≤ ENNReal.ofReal (diam A) := h_diam_lower
      have h4 : ENNReal.ofReal V ≤ volume (ExpansionLemma.scaledSumset v A) := hvol
      have h5 : ENNReal.ofReal (V^2 / (2 * (m : ℝ))) =
          ENNReal.ofReal (V / (2 * (m : ℝ))) * ENNReal.ofReal V := by
        have h_nonneg : 0 ≤ V / (2 * (m : ℝ)) := by positivity
        rw [←ENNReal.ofReal_mul h_nonneg] <;> ring_nf
      rw [h5]
      gcongr
    exact le_trans h2 h1
  exact ⟨hA'_compact, hA'_nonempty, hA'_bdd, hV'_pos, h_vol_new⟩

/-- Quantitative iterative elimination induction.

Given compact nonempty `A` with radius bound `R0`, weights `v : Fin n → ℝ` in `[1/2,1]`,
and volume lower bound `V0` for `scaledSumset v A`, produces `d, M, V_final` such that
`volume(iteratedDifference (productSet A d) M) ≥ V_final`.

The parameters `d, M, V_final` depend only on `n, R0, V0` and the uniform expansion lemma,
not on the specific `A` or `v`. -/
theorem quantitative_elimination_induction
    (h_expansion_uniform : ∀ (m : ℕ), 2 ≤ m → ∀ (d_max lam_min : ℝ),
      0 < d_max → 0 < lam_min →
      ∃ (N_max : ℕ), ∀ (A : Set ℝ), IsCompact A → A.Nonempty → diam A ≤ d_max →
        ∀ (v : Fin m → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
          ENNReal.ofReal lam_min ≤ volume (ExpansionLemma.scaledSumset v A) →
          ∃ (j : Fin m),
            volume (ExpansionLemma.scaledSumsetExcept v j
              (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N_max)) ≥
            ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A)) :
    ∀ (n : ℕ) (R0 V0 : ℝ), 0 < R0 → 0 < V0 →
      ∃ (d M : ℕ) (V_final : ℝ), 1 ≤ d ∧ 0 < V_final ∧
        ∀ (A : Set ℝ), IsCompact A → A.Nonempty → A ⊆ Set.Icc (-R0) R0 →
          ∀ (v : Fin n → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
            ENNReal.ofReal V0 ≤ volume (ExpansionLemma.scaledSumset v A) →
              ENNReal.ofReal V_final ≤ volume (ExpansionLemma.iteratedDifference
                (ExpansionLemma.productSet A d) M) := by
  intro n
  induction n with
  | zero =>
    intro R0 V0 hR0_pos hV0_pos
    refine ⟨1, 1, V0, by norm_num, hV0_pos, ?_⟩
    intro A hA hA_nonempty hA_bdd v hv hvol
    have h0 : ExpansionLemma.scaledSumset v A = {0} := by
      ext x
      simp [ExpansionLemma.scaledSumset]
      <;> constructor <;> intro h <;> simpa using h
    rw [h0] at hvol
    simp at hvol <;> linarith
  | succ n ih =>
    intro R0 V0 hR0_pos hV0_pos
    by_cases h_n : n = 0
    · -- Base case: n+1 = 1 weight
      subst h_n
      refine ⟨1, 1, V0, by norm_num, hV0_pos, ?_⟩
      intro A hA hA_nonempty hA_bdd v hv hvol
      have h_v0_pos : 0 < v 0 := by have h := (hv 0).1; linarith
      have h_v0_ne : v 0 ≠ 0 := h_v0_pos.ne'
      have h_ss : ExpansionLemma.scaledSumset v A = (fun x : ℝ => v 0 * x) '' A := by
        ext y
        simp only [ExpansionLemma.scaledSumset, Set.mem_setOf_eq, Set.mem_image]
        constructor
        · rintro ⟨a, ha, h_eq⟩
          have h_sum : ∑ i : Fin 1, v i * a i = v 0 * a 0 := by rw [Fin.sum_univ_one] <;> rfl
          rw [h_sum] at h_eq; exact ⟨a 0, ha 0, h_eq.symm⟩
        · rintro ⟨x, hx, h_eq⟩
          let a : Fin 1 → ℝ := fun _ => x
          have ha : ∀ i, a i ∈ A := by intro i; simpa [a] using hx
          have h_sum : ∑ i : Fin 1, v i * a i = v 0 * x := by rw [Fin.sum_univ_one] <;> simp [a] <;> ring
          exact ⟨a, ha, by rw [h_sum, h_eq]⟩
      rw [h_ss] at hvol
      -- volume(v0 * A) = |v0| * volume(A)
      have h_vol_image : volume ((fun x : ℝ => v 0 * x) '' A) =
          ENNReal.ofReal (|v 0|) * volume A := by
        have h_image_eq : (fun x : ℝ => v 0 * x) '' A =
            (fun y : ℝ => y / (v 0)) ⁻¹' A := by
          ext z
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa [h_v0_ne] using hx
          · intro hz
            refine ⟨z / (v 0), hz, ?_⟩
            field_simp [h_v0_ne] <;> ring
        rw [h_image_eq]
        have h_div : (fun y : ℝ => y / (v 0)) = fun y : ℝ => y * (v 0)⁻¹ := by
          funext y; field_simp
        rw [h_div]
        rw [Real.volume_preimage_mul_right (inv_ne_zero h_v0_ne) A]
        have h_abs : |((v 0)⁻¹)⁻¹| = |v 0| := by rw [inv_inv]
        rw [h_abs]
      rw [h_vol_image] at hvol
      have h2 : |v 0| ≤ 1 := by have h3 := (hv 0).2; exact abs_le.mpr ⟨by linarith, by linarith⟩
      have h4 : ENNReal.ofReal (|v 0|) ≤ 1 := by
        have h5 : |v 0| ≤ 1 := h2
        have h6 : ENNReal.ofReal (|v 0|) ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal_iff'.mpr (Or.inl h5)
        rw [ENNReal.ofReal_one] at h6
        exact h6
      have h_volA : ENNReal.ofReal V0 ≤ volume A := by
        calc ENNReal.ofReal V0
          ≤ ENNReal.ofReal (|v 0|) * volume A := hvol
        _ ≤ 1 * volume A := by gcongr
        _ = volume A := by simp
      rcases hA_nonempty with ⟨a, ha⟩
      have h_translate : (fun x : ℝ => x - a) '' A ⊆ ExpansionLemma.iteratedDifference A 1 := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        simp [ExpansionLemma.iteratedDifference, ExpansionLemma.iteratedSumset]
        <;> exact ⟨x, hx, a, ha, by ring⟩
      have h_vol_translate : ENNReal.ofReal V0 ≤ volume ((fun x : ℝ => x - a) '' A) := by
        have h_eq : volume ((fun x : ℝ => x - a) '' A) = volume A := by
          have h_image_eq : (fun x : ℝ => x - a) '' A = (fun y : ℝ => y + a) ⁻¹' A := by
            ext z
            simp only [Set.mem_image, Set.mem_preimage]
            constructor
            · rintro ⟨x, hx, rfl⟩; simpa using hx
            · intro hz; refine ⟨z + a, hz, ?_⟩; ring
          rw [h_image_eq]
          simpa using Real.volume_preimage_add a A
        rw [h_eq]
        exact h_volA
      have h_ps1 : ExpansionLemma.productSet A 1 = A := by
        ext x
        simp only [ExpansionLemma.productSet, Set.mem_setOf_eq]
        constructor
        · rintro ⟨f, hf, h_eq⟩
          have h : ∏ i : Fin 1, f i = f 0 := by simp
          rw [h] at h_eq
          rw [h_eq] <;> exact hf 0
        · intro hx
          refine ⟨fun _ => x, fun _ => hx, ?_⟩
          simp
      rw [h_ps1]
      exact le_trans h_vol_translate (measure_mono h_translate)
    · -- Inductive step: n+1 ≥ 2 weights
      have h_n2 : 2 ≤ n + 1 := by omega
      -- Get N from uniform expansion lemma
      rcases h_expansion_uniform (n + 1) h_n2 (2 * R0) V0 (by positivity) hV0_pos with ⟨N_raw, hN_raw⟩
      -- Ensure N ≥ 1 by taking max with 1. Larger N still works because
      -- iteratedDifference is monotone in N for nonempty sets.
      let N : ℕ := max N_raw 1
      have hN_ge_raw : N_raw ≤ N := le_max_left _ _
      have hN_pos : 0 < N := by
        dsimp only [N]
        exact Nat.lt_succ_iff.mp (Nat.lt_succ_iff.mpr (le_max_right _ _))
      -- Prove that N also satisfies the expansion lemma conclusion
      have hN : ∀ (A : Set ℝ), IsCompact A → A.Nonempty → diam A ≤ 2 * R0 →
          ∀ (v : Fin (n + 1) → ℝ), (∀ i, v i ∈ Set.Icc (1 / 2 : ℝ) 1) →
            ENNReal.ofReal V0 ≤ volume (ExpansionLemma.scaledSumset v A) →
            ∃ (j : Fin (n + 1)),
              volume (ExpansionLemma.scaledSumsetExcept v j
                (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N)) ≥
              ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) := by
        intro A hA hA_nonempty h_diam v hv hvol
        rcases hN_raw A hA hA_nonempty h_diam v hv hvol with ⟨j, h_j⟩
        let S := ExpansionLemma.productSet A 2
        have hS_nonempty : S.Nonempty := by
          rcases hA_nonempty with ⟨a, ha⟩
          refine ⟨a * a, ?_⟩
          refine ⟨fun _ => a, fun _ => ha, ?_⟩
          rw [Fin.prod_univ_two] <;> simp
        have h_mono : ExpansionLemma.iteratedDifference S N_raw ⊆
            ExpansionLemma.iteratedDifference S N :=
          WeakTwoEndsSumProduct.iteratedDifference_pad_sum hS_nonempty hN_ge_raw
        have h_ss_mono : ExpansionLemma.scaledSumsetExcept v j
            (ExpansionLemma.iteratedDifference S N_raw) ⊆
          ExpansionLemma.scaledSumsetExcept v j (ExpansionLemma.iteratedDifference S N) := by
          intro z hz
          simp only [ExpansionLemma.scaledSumsetExcept, ExpansionLemma.scaledSumset,
            Set.mem_setOf_eq] at hz ⊢
          rcases hz with ⟨a, ha, rfl⟩
          exact ⟨a, fun i => h_mono (ha i), rfl⟩
        refine ⟨j, le_trans h_j (measure_mono h_ss_mono)⟩
      set R1 : ℝ := 2 * (N : ℝ) * R0^2 with hR1_def
      set V1 : ℝ := V0^2 / (2 * (↑n + 1)) with hV1_def
      have hR1_pos : 0 < R1 := by
        dsimp only [R1]
        have h1 : 0 < (N : ℝ) := by exact_mod_cast hN_pos
        positivity
      have hV1_pos : 0 < V1 := by
        dsimp only [V1]
        apply div_pos
        · exact sq_pos_of_pos hV0_pos
        · have h_pos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
          exact h_pos
      rcases ih R1 V1 hR1_pos hV1_pos with ⟨d, M, V_final, hd_pos, hV_final_pos, h_ih⟩
      -- Flattening: lift result from A' back to A
      let e_idx : ℕ := d - 1
      have h_d_eq : d = e_idx + 1 := by omega
      let B : ℕ := N ^ d * 2 ^ e_idx
      let d_final : ℕ := 2 * d
      let M_final : ℕ := 2 * M * B
      have hd_final_pos : 1 ≤ d_final := by omega
      refine ⟨d_final, M_final, V_final, hd_final_pos, hV_final_pos, ?_⟩
      intro A hA hA_nonempty hA_bdd v hv hvol
      -- Apply uniform expansion with our chosen N
      have h_diam : diam A ≤ 2 * R0 := by
        have h2 : Bornology.IsBounded (Set.Icc (-R0) R0) := isCompact_Icc.isBounded
        have h3 : diam A ≤ diam (Set.Icc (-R0) R0) := diam_mono hA_bdd h2
        have h4 : diam (Set.Icc (-R0) R0) = 2 * R0 := by
          rw [Real.diam_Icc (by linarith)] <;> ring
        rw [h4] at h3; exact h3
      rcases hN A hA hA_nonempty h_diam v hv hvol with ⟨j, hvol'⟩
      let A' := ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N
      let ι := {i : Fin (n + 1) // i ≠ j}
      let w : ι → ℝ := fun i => v i
      have hw : ∀ i : ι, w i ∈ Set.Icc (1 / 2 : ℝ) 1 := fun i => hv i
      have h_card : Fintype.card ι = n := by
        simp [ι, Fintype.card_subtype_compl] <;> omega
      let e2 : Fin (Fintype.card ι) ≃ Fin n :=
        { toFun := Fin.cast h_card
          invFun := Fin.cast h_card.symm
          left_inv := by intro x; simp
          right_inv := by intro x; simp }
      let e : ι ≃ Fin n := (Fintype.equivFin ι).trans e2
      let v' : Fin n → ℝ := fun k => w (e.symm k)
      have hv' : ∀ k : Fin n, v' k ∈ Set.Icc (1 / 2 : ℝ) 1 := fun k => hw (e.symm k)
      have h_eq_ss : ExpansionLemma.scaledSumset v' A' = ExpansionLemma.scaledSumset w A' := by
        have h := WeakTwoEndsSumProduct.scaledSumset_equiv (e.symm) (v := w) (A := A')
        convert h <;> funext k <;> rfl
      -- Prove A' properties
      have hA'_compact : IsCompact A' :=
        WeakTwoEndsSumProduct.iteratedDifference_compact
          (WeakTwoEndsSumProduct.productSet_compact hA)
      have hPS_nonempty : (ExpansionLemma.productSet A 2).Nonempty := by
        rcases hA_nonempty with ⟨a, ha⟩
        refine ⟨a * a, ?_⟩
        refine ⟨fun _ => a, fun _ => ha, ?_⟩
        rw [Fin.prod_univ_two] <;> simp
      have hA'_nonempty : A'.Nonempty := by
        have h_sum_nonempty : (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N).Nonempty := by
          have h_main : ∀ (k : ℕ), (ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) k).Nonempty := by
            intro k
            induction k with
            | zero => simp [ExpansionLemma.iteratedSumset] <;> exact ⟨0, by simp⟩
            | succ k ih =>
              rcases hPS_nonempty with ⟨s, hs⟩
              rcases ih with ⟨x, hx⟩
              exact ⟨s + x, ⟨s, hs, x, hx, rfl⟩⟩
          exact h_main N
        rcases h_sum_nonempty with ⟨x, hx⟩
        have h0 : (0 : ℝ) ∈ A' := by
          simp only [A', ExpansionLemma.iteratedDifference]
          exact ⟨x, hx, x, hx, by ring⟩
        exact ⟨0, h0⟩
      have hA'_bdd : A' ⊆ Set.Icc (-R1) R1 := by
        have hR0_nonneg : 0 ≤ R0 := by linarith
        have h1 : ExpansionLemma.productSet A 2 ⊆ Set.Icc (-(R0^2)) (R0^2) := by
          intro z hz
          have h_exists : ∃ (a : Fin 2 → ℝ), (∀ i, a i ∈ A) ∧ z = ∏ i : Fin 2, a i := by
            simpa [ExpansionLemma.productSet] using hz
          rcases h_exists with ⟨a, ha, h_eq⟩
          have h3 : a 0 ∈ Set.Icc (-R0) R0 := hA_bdd (ha 0)
          have h4 : a 1 ∈ Set.Icc (-R0) R0 := hA_bdd (ha 1)
          have h5 : -R0^2 ≤ a 0 * a 1 := by nlinarith [h3.1, h3.2, h4.1, h4.2]
          have h6 : a 0 * a 1 ≤ R0^2 := by nlinarith [h3.1, h3.2, h4.1, h4.2]
          have h_prod : (∏ i : Fin 2, a i) = a 0 * a 1 := by simp [Fin.prod_univ_two] <;> ring
          rw [h_eq, h_prod]; exact ⟨h5, h6⟩
        have h2 : ExpansionLemma.iteratedSumset (ExpansionLemma.productSet A 2) N ⊆
            Set.Icc (-(N : ℝ) * R0^2) ((N : ℝ) * R0^2) :=
          WeakTwoEndsSumProduct.iteratedSumset_bounded (N := N) (by positivity) h1
        intro z hz
        rcases hz with ⟨x, hx, y, hy, rfl⟩
        have hx' := h2 hx
        have hy' := h2 hy
        have h_z1 : -R1 ≤ x - y := by
          dsimp only [R1]; nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
        have h_z2 : x - y ≤ R1 := by
          dsimp only [R1]; nlinarith [hx'.1, hx'.2, hy'.1, hy'.2]
        exact ⟨h_z1, h_z2⟩
      -- Volume lower bound for V1
      have h_diam_lower : ENNReal.ofReal (V0 / (2 * (↑n + 1))) ≤ ENNReal.ofReal (diam A) := by
        have h_raw := WeakTwoEndsSumProduct.diam_lower_from_scaledSumset_volume hA_nonempty (IsCompact.isBounded hA) hv hvol hV0_pos (by linarith)
        have h_eq : (V0 / (2 * ↑(n + 1))) = (V0 / (2 * (↑n + 1))) := by norm_cast
        rw [h_eq] at h_raw
        exact h_raw
      have h_vol_v1 : ENNReal.ofReal V1 ≤
          volume (ExpansionLemma.scaledSumsetExcept v j A') := by
        dsimp only [V1]
        have h1 : ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) ≤
            volume (ExpansionLemma.scaledSumsetExcept v j A') := hvol'
        have h2 : ENNReal.ofReal (V0^2 / (2 * (↑n + 1))) ≤
            ENNReal.ofReal (diam A) * volume (ExpansionLemma.scaledSumset v A) := by
          have h3 : ENNReal.ofReal (V0 / (2 * (↑n + 1))) ≤ ENNReal.ofReal (diam A) := h_diam_lower
          have h4 : ENNReal.ofReal V0 ≤ volume (ExpansionLemma.scaledSumset v A) := hvol
          have h5 : ENNReal.ofReal (V0^2 / (2 * (↑n + 1))) =
              ENNReal.ofReal (V0 / (2 * (↑n + 1))) * ENNReal.ofReal V0 := by
            have h_nonneg : 0 ≤ V0 / (2 * (↑n + 1)) := by positivity
            rw [←ENNReal.ofReal_mul h_nonneg] <;> ring_nf
          rw [h5]
          gcongr
        exact le_trans h2 h1
      have h_vol_v' : ENNReal.ofReal V1 ≤ volume (ExpansionLemma.scaledSumset v' A') := by
        have h_eq : ExpansionLemma.scaledSumsetExcept v j A' = ExpansionLemma.scaledSumset w A' := by rfl
        rw [h_eq] at h_vol_v1
        rw [h_eq_ss]
        exact h_vol_v1
      have h_vol_result : ENNReal.ofReal V_final ≤
          volume (ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A' d) M) :=
        h_ih A' hA'_compact hA'_nonempty hA'_bdd v' hv' h_vol_v'
      -- Flattening step 1: productSet A' d ⊆ iteratedDifference (productSet A d_final) B
      have h_contain : A' ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) N :=
        subset_refl A'
      have h_productSet_contain : ExpansionLemma.productSet A' d ⊆
          ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d_final) B := by
        have h_goal := WeakTwoEndsSumProduct.productSet_of_iteratedDifference e_idx h_contain
        have h_d : d = e_idx + 1 := h_d_eq
        have h_final : ExpansionLemma.productSet A' d ⊆
            ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d_final) B := by
          have h_df : d_final = 2 * d := by rfl
          have h_B : B = N ^ d * 2 ^ e_idx := by rfl
          rw [h_df, h_B, h_d_eq]
          exact h_goal
        exact h_final
      have hPS_nonempty : (ExpansionLemma.productSet A' d).Nonempty := by
        rcases hA'_nonempty with ⟨x, hx⟩
        refine ⟨x ^ d, ?_⟩
        refine ⟨fun _ => x, fun _ => hx, ?_⟩
        have h : ∏ i : Fin d, (fun _ : Fin d => x) i = x ^ d := by
          simp [Finset.prod_const] <;> ring
        exact h.symm
      -- Flattening step 2: iteratedDifference (productSet A' d) M ⊆ iteratedDifference (productSet A d_final) M_final
      have h_diff_contain : ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A' d) M ⊆
          ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A d_final) M_final :=
        WeakTwoEndsSumProduct.difference_of_difference h_productSet_contain hPS_nonempty
      exact le_trans h_vol_result (measure_mono h_diff_contain)

/-- Flattening lemma (no `1 ∈ A` required).

Shows that a chain of iteratedDifferences is contained in a single
`iteratedDifference (productSet A d) M` for sufficiently large `d, M`.

Uses `iterated_containment_gen_explicit` for the induction, which avoids
any padding assumption. Outputs separate `d` and `M` rather than forcing
them equal; use `iteratedDifference_pad_product` + `volume_dilation` +
`iteratedDifference_pad_sum` if a single `N` is needed.

Requires `1 ≤ n` since the base case `n=0` would need
`A ⊆ iteratedDifference(productSet A d) M`, which is false in general. -/
lemma flatten_chain
    {A : Set ℝ} {n : ℕ} (chain : ℕ → Set ℝ) (N_chain : ℕ → ℕ)
    (h_chain : ∀ k < n, chain (k + 1) = ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet (chain k) 2) (N_chain k))
    (hA0 : chain 0 = A) (hn : 1 ≤ n) :
    ∃ (d M : ℕ), chain n ⊆ ExpansionLemma.iteratedDifference
      (ExpansionLemma.productSet A d) M := by
  let d : ℕ → ℕ := fun k => 2 ^ k
  let M : ℕ → ℕ := fun k => Nat.recOn k 0 fun k prev =>
    if k = 0 then N_chain 0 else 8 * N_chain k * prev^2
  have hM1 : M 1 = N_chain 0 := by
    simp [M] <;> omega
  have hM_succ : ∀ k : ℕ, M (k + 2) = 8 * N_chain (k + 1) * (M (k + 1)) ^ 2 := by
    intro k
    simp [M] <;> split_ifs <;> ring_nf <;> omega
  have h_main : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      chain k ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d k)) (M k) := by
    intro k hk1 hkn
    induction k with
    | zero =>
      exfalso; linarith
    | succ k ih =>
      by_cases h_k : k = 0
      · -- Base case k=1
        have h_k0 : k = 0 := h_k
        have h1 : chain 1 = ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A 2) (N_chain 0) := by
          rw [h_chain 0 (by linarith), hA0]
        have hd1 : d 1 = 2 := by simp [d]
        have h_goal : chain 1 ⊆ ExpansionLemma.iteratedDifference (ExpansionLemma.productSet A (d 1)) (M 1) := by
          rw [h1, hd1, hM1]
          <;> exact Subset.refl _
        simpa [h_k0] using h_goal
      · -- Inductive step k ≥ 1
        have h_k1 : 1 ≤ k := by omega
        have h_ih := ih h_k1 (by omega)
        have h_chain_k : chain (k + 1) = ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet (chain k) 2) (N_chain k) := h_chain k (by omega)
        rw [h_chain_k]
        have h_contain : chain k ⊆ ExpansionLemma.iteratedDifference
            (ExpansionLemma.productSet A (d k)) (M k) := h_ih
        have h := WeakTwoEndsSumProduct.iterated_containment_gen_explicit A (chain k) (d k) (M k) 2 (N_chain k) (by norm_num) h_contain
        have h_d_succ : d (k + 1) = 2 * d k := by
          simp [d, pow_succ] <;> ring
        have h_M_succ : M (k + 1) = 2 * (N_chain k) * (2 ^ 2 * (M k) ^ 2) := by
          cases k with
          | zero => contradiction
          | succ k' =>
            simpa [hM_succ] using by ring
        rw [h_d_succ, h_M_succ]
        exact h
  have h_final := h_main n hn (by linarith)
  exact ⟨d n, M n, h_final⟩

end RecursiveElimination
