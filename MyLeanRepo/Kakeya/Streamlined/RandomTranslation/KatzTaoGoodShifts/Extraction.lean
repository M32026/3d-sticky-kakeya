import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.ConflictColoring
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.EssentiallyDistinctSubfamily
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.TotalConflictExtraction
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers
import Mathlib.Tactic

/-!
# Average-degree ED extraction and deltaMax transfer

Given a finite conflict graph with bounded average degree, remove high-degree
vertices and apply bounded-degree conflict-free coloring to extract a large
essentially-distinct subfamily.  Also provides deltaMax monotonicity for
subfamilies and polynomial-loss absorption helpers.

## Main results

- `extract_ed_of_avg_degree`: if total conflict degree ≤ 8·|G|, there exists an
  ED subfamily S with |G| ≤ 34·|S|.
- `tubeSubfamily_deltaMax_le`: deltaMax is monotone under subfamilies.
- `exists_delta₀_rpow_eta_le_inv`: δ^η ≤ 1/34 for small δ.
- `log_absorbed_by_rpow_neg_eta`: A·log(1/δ) + const is O(δ^{-η}).
-/

noncomputable section

open MeasureTheory Finset Classical

namespace Kakeya.Streamlined

/-- **Average-degree essentially-distinct extraction.**

Given a tube family `G` whose total conflict degree (sum of pairwise
non-ED neighbor counts) is at most `8 · |G|`, there exists a nonempty
essentially-distinct subfamily `S` with `|G| ≤ 34 · |S|`.

Proof: remove vertices of degree > 16 (at most `8n/17` of them), then apply
bounded-degree conflict-free selection with `D = 16` to the remaining `≥ 9n/17`
vertices, retaining at least a `1/17` fraction.  The product gives
`9/289 > 1/34`. -/
lemma extract_ed_of_avg_degree
    {δ : ℝ} {G : TubeFamily δ}
    (hG_nonempty : G.Nonempty)
    (h_conflict : tubeTotalConflictDegree G ≤ 8 * G.card) :
    ∃ S : TubeSubfamily G,
      S.Nonempty ∧
      S.family.IsEssentiallyDistinct ∧
      G.enncard ≤ 34 * S.family.enncard := by
  classical
  let conflict : Fin G.card → Fin G.card → Prop :=
    fun i j => ¬(G.tube i).EssentiallyDistinct (G.tube j)
  have hsymm : ∀ ⦃i j⦄, conflict i j → conflict j i := by
    intro i j h
    exact essentiallyDistinct_symm.not.mp h

  let high : Finset (Fin G.card) :=
    Finset.univ.filter fun i => tubeConflictDegree G i > 16
  let low : Finset (Fin G.card) := Finset.univ \ high

  have hhigh_degree : ∀ i ∈ high, 17 ≤ tubeConflictDegree G i := by
    intro i hi
    have h : tubeConflictDegree G i > 16 := (Finset.mem_filter.mp hi).2
    exact Nat.succ_le_iff.mpr h

  have hhigh_sum : ∑ i ∈ high, tubeConflictDegree G i ≤ tubeTotalConflictDegree G := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ high
    · intro _ _ _; exact Nat.zero_le _

  have hhigh_card : high.card * 17 ≤ 8 * G.card := by
    calc
      high.card * 17
        = ∑ _i ∈ high, 17 := by simp [Finset.sum_const]
      _ ≤ ∑ i ∈ high, tubeConflictDegree G i := by
        apply Finset.sum_le_sum; intro i hi; exact hhigh_degree i hi
      _ ≤ tubeTotalConflictDegree G := hhigh_sum
      _ ≤ 8 * G.card := h_conflict

  have h_partition : low.card + high.card = G.card := by
    have h_disj : Disjoint low high := by
      simp [low, high, Finset.disjoint_left] <;> tauto
    have h_union : low ∪ high = Finset.univ := by
      simp [low, high] <;> tauto
    have h := Finset.card_union_of_disjoint h_disj
    rw [h_union] at h
    simpa using h.symm

  have hlow_card : 17 * low.card ≥ 9 * G.card := by
    omega

  have hdegree : ∀ i ∈ low,
      (low.filter fun j => j ≠ i ∧ conflict i j).card ≤ 16 := by
    intro i hi
    have h1 : tubeConflictDegree G i ≤ 16 := by
      have h2 : i ∉ high := by
        simpa [low, high] using (Finset.mem_sdiff.mp hi).2
      simpa [high, Finset.mem_filter] using h2
    have h3 : (low.filter fun j => j ≠ i ∧ conflict i j) ⊆
        (Finset.univ.filter fun j => j ≠ i ∧ conflict i j) := by
      intro j hj
      have h4 := (Finset.mem_filter.mp hj)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h4.2⟩
    calc
      (low.filter fun j => j ≠ i ∧ conflict i j).card
        ≤ (Finset.univ.filter fun j => j ≠ i ∧ conflict i j).card :=
          Finset.card_le_card h3
      _ = tubeConflictDegree G i := rfl
      _ ≤ 16 := h1

  let weight : Fin G.card → ENNReal := fun _ => 1

  rcases exists_heavy_bounded_conflict_free_class
      low 16 weight conflict hsymm hdegree with
    ⟨selected, hselected_sub, hselected_free, hmass⟩

  have hcard : low.card ≤ 17 * selected.card := by
    have h5 : (∑ i ∈ low, weight i) ≤ ((17 : ℕ) : ENNReal) * ∑ i ∈ selected, weight i := hmass
    have h6 : (low.card : ENNReal) ≤ (17 : ENNReal) * (selected.card : ENNReal) := by
      simpa [weight, Finset.sum_const] using h5
    exact_mod_cast h6

  have hmain : G.card ≤ 34 * selected.card := by
    omega

  let S : TubeSubfamily G := TubeSubfamily.fromFinset G selected

  have hS_ed : S.family.IsEssentiallyDistinct := by
    intro i j hne
    have hi : S.embedding i ∈ selected := Finset.orderEmbOfFin_mem selected rfl i
    have hj : S.embedding j ∈ selected := Finset.orderEmbOfFin_mem selected rfl j
    have hne' : S.embedding i ≠ S.embedding j := fun h => hne (S.embedding.inj' h)
    rw [S.tube_eq i, S.tube_eq j]
    exact Classical.byContradiction fun hconflict =>
      hselected_free (S.embedding i) hi (S.embedding j) hj hne' hconflict

  have hS_card_eq : S.family.enncard = (selected.card : ENNReal) := by
    simp [S, TubeSubfamily.fromFinset, TubeFamily.enncard] <;> rfl

  have hS_nonempty : S.Nonempty := by
    have h9 : 0 < G.card := hG_nonempty
    have h10 : G.card ≤ 34 * selected.card := hmain
    have h11 : 0 < selected.card := by omega
    exact h11

  refine ⟨S, hS_nonempty, hS_ed, ?_⟩
  rw [hS_card_eq]
  have hgoal : (G.card : ENNReal) ≤ (34 : ENNReal) * (selected.card : ENNReal) := by
    exact_mod_cast hmain
  exact hgoal

/-- **deltaMax monotonicity for tube subfamilies.**

If `S` is a subfamily of `F`, then `S.family.toBodyFamily.deltaMax ≤ F.toBodyFamily.deltaMax`.
This follows from the generic `subfamily_deltaMax_le`. -/
lemma tubeSubfamily_deltaMax_le
    {δ : ℝ} {F : TubeFamily δ} (S : TubeSubfamily F) :
    S.family.toBodyFamily.deltaMax ≤ F.toBodyFamily.deltaMax :=
  subfamily_deltaMax_le S.toBodySubfamily

/-- For any `η > 0` and `c > 0`, there exists `δ₀ > 0` such that
`δ^η ≤ 1/c` for all `0 < δ ≤ δ₀`. -/
lemma exists_delta₀_rpow_eta_le_inv
    {η c : ℝ} (hη : 0 < η) (hc : 0 < c) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ, 0 < δ → δ ≤ δ₀ → δ ^ η ≤ 1 / c := by
  by_cases h : c ≥ 1
  · -- c ≥ 1: δ₀ = (1/c)^(1/η) ≤ 1
    let δ₀ : ℝ := (1 / c) ^ (1 / η)
    have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos (by positivity) _
    have h1 : 0 ≤ 1 / c := by positivity
    have h2 : 1 / c ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    have hδ₀_le_one : δ₀ ≤ 1 := by
      dsimp only [δ₀]
      exact Real.rpow_le_one h1 h2 (by positivity)
    refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
    intro δ hδ_pos hδ_le
    have h3 : δ ^ η ≤ δ₀ ^ η := by gcongr <;> linarith
    have h4 : δ₀ ^ η = 1 / c := by
      dsimp only [δ₀]
      have h_pos : 0 < 1 / c := by positivity
      have h5 : ((1 / c) ^ (1 / η)) ^ η = (1 / c) ^ ((1 / η) * η) := by
        rw [← Real.rpow_mul (by linarith)] <;> ring
      rw [h5]
      have h6 : (1 / η) * η = 1 := by field_simp [hη.ne'] <;> ring
      rw [h6] <;> simp
    rw [h4] at h3
    exact h3
  · -- c < 1: δ₀ = 1, and δ^η ≤ 1 < 1/c for δ ≤ 1
    have hc_lt_one : c < 1 := by linarith
    let δ₀ : ℝ := 1
    have hδ₀_pos : 0 < δ₀ := by norm_num
    have hδ₀_le_one : δ₀ ≤ 1 := by norm_num
    refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
    intro δ hδ_pos hδ_le
    have h3 : δ ^ η ≤ 1 := by
      have h4 : 0 ≤ δ := by linarith
      have h5 : δ ≤ 1 := by linarith
      exact Real.rpow_le_one h4 h5 (by linarith)
    have h6 : (1 : ℝ) < 1 / c := by
      have h7 : 1 / c > 1 / 1 := by gcongr
      simpa using h7
    linarith

/-- ENNReal version: `realRpowENN δ η ≤ 34⁻¹` for sufficiently small `δ`. -/
lemma exists_delta₀_rpowENN_eta_le_inv34
    {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ, 0 < δ → δ ≤ δ₀ →
        Kakeya.realRpowENN δ η ≤ (34 : ENNReal)⁻¹ := by
  rcases exists_delta₀_rpow_eta_le_inv hη (show (0 : ℝ) < 34 by norm_num) with
    ⟨δ₀, hδ₀_pos, hδ₀_le_one, h⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro δ hδ_pos hδ_le
  have h6 : δ ^ η ≤ 1 / 34 := h δ hδ_pos hδ_le
  have h7 : 0 ≤ δ ^ η := by positivity
  have h8 : ENNReal.ofReal (δ ^ η) ≤ ENNReal.ofReal (1 / 34) :=
    ENNReal.ofReal_le_ofReal h6
  have h9 : (34 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 34) := by
    have h11 : (ENNReal.ofReal (34 : ℝ))⁻¹ = ENNReal.ofReal ((34 : ℝ)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 34 by norm_num)).symm
    have h12 : (34 : ℝ)⁻¹ = 1 / 34 := by norm_num
    have h13 : (34 : ENNReal) = ENNReal.ofReal (34 : ℝ) := by norm_cast
    rw [h13, h11, h12]
  have h10 : Kakeya.realRpowENN δ η = ENNReal.ofReal (δ ^ η) := by
    rfl
  rw [h10, h9]
  exact h8

/-- **Logarithmic absorption by negative power.**

For any `η > 0` and real `A ≥ 0`, there exists a nonnegative real constant `C`
such that for all `0 < δ ≤ 1`:
`A * Real.log (1 / δ) ≤ C * δ ^ (-η)`.

Proof: use `Real.log_le_rpow_div` with exponent `η/2`, then convert to
`δ^(-η/2) ≤ δ^(-η)` via `x = 1/δ ≥ 1`. -/
lemma log_absorbed_by_rpow_neg_eta
    {η A : ℝ} (hη : 0 < η) (hA : 0 ≤ A) :
    ∃ (C : ℝ), 0 ≤ C ∧
      ∀ δ, 0 < δ → δ ≤ 1 →
        A * Real.log (1 / δ) ≤ C * δ ^ (-η) := by
  set ε : ℝ := η / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have hε_le_eta : ε ≤ η := by linarith
  let C : ℝ := A / ε
  have hC_nonneg : 0 ≤ C := by positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro δ hδ_pos hδ_le_one
  set x : ℝ := 1 / δ with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have hx_ge_one : 1 ≤ x := by
    dsimp only [x]
    have h : 1 / δ ≥ 1 / 1 := by gcongr
    simpa using h
  have h1 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx_nonneg hε_pos
  have h2 : A * Real.log x ≤ A * (x ^ ε / ε) := by gcongr
  have h3 : x ^ ε ≤ x ^ η := Real.rpow_le_rpow_of_exponent_le hx_ge_one hε_le_eta
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h4 : x ^ η = δ ^ (-η) := by
    dsimp only [x]
    have h5 : (1 / δ) ^ η = (δ ^ η)⁻¹ := by
      have h6 : (1 / δ) = δ⁻¹ := by field_simp [hδ_pos.ne']
      rw [h6]
      exact Real.inv_rpow hδ_nonneg η
    rw [h5]
    have h7 : (δ ^ η)⁻¹ = δ ^ (-η) := by
      rw [← Real.rpow_neg hδ_nonneg] <;> ring
    exact h7
  calc
    A * Real.log (1 / δ)
      = A * Real.log x := by rfl
    _ ≤ A * (x ^ ε / ε) := h2
    _ = (A / ε) * x ^ ε := by ring
    _ ≤ (A / ε) * x ^ η := by gcongr
    _ = (A / ε) * δ ^ (-η) := by rw [h4]
    _ = C * δ ^ (-η) := by rfl

/-- **Constant and logarithmic absorption by negative power (ENNReal).**

For any `η > 0`, `A ≥ 0`, and constant `B : ℝ`, there exists `C : ENNReal`
with `C ≠ ⊤` such that for all `0 < δ ≤ 1`:
`ENNReal.ofReal (B + A * Real.log (1 / δ)) ≤ C * Kakeya.realRpowENN δ (-η)`,
provided the left side is well-defined (nonnegative).

This absorbs both the constant `B` and the logarithmic term `A · log(1/δ)`. -/
lemma const_log_absorbed_by_rpow_neg_eta
    {η A B : ℝ} (hη : 0 < η) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      ∀ δ, 0 < δ → δ ≤ 1 →
        ENNReal.ofReal (B + A * Real.log (1 / δ)) ≤
          C * Kakeya.realRpowENN δ (-η) := by
  rcases log_absorbed_by_rpow_neg_eta hη hA with ⟨C_log, hC_log_nonneg, hlog⟩
  let C_real : ℝ := B + C_log
  have hC_nonneg : 0 ≤ C_real := by
    dsimp only [C_real]
    linarith
  let C : ENNReal := ENNReal.ofReal C_real
  have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨C, hC_ne_top, ?_⟩
  intro δ hδ_pos hδ_le_one
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h_deta_pos : 0 < δ ^ η := Real.rpow_pos_of_pos hδ_pos η
  have h_deta_le_one : δ ^ η ≤ 1 :=
    Real.rpow_le_one hδ_nonneg hδ_le_one (by linarith)
  have h3 : 1 ≤ δ ^ (-η) := by
    have h4 : δ ^ (-η) = (δ ^ η)⁻¹ := by
      rw [Real.rpow_neg hδ_nonneg] <;> ring
    rw [h4]
    have h5 : (δ ^ η)⁻¹ ≥ 1 := by
      have h6 : δ ^ η ≤ 1 := h_deta_le_one
      have h7 : 0 < δ ^ η := h_deta_pos
      calc
        1 = (1 : ℝ)⁻¹ := by simp
        _ ≤ (δ ^ η)⁻¹ := by gcongr
    exact h5
  have h2 : B ≤ B * δ ^ (-η) := by
    calc
      B = B * 1 := by ring
      _ ≤ B * δ ^ (-η) := by gcongr
  have h4 : A * Real.log (1 / δ) ≤ C_log * δ ^ (-η) :=
    hlog δ hδ_pos hδ_le_one
  have h1 : B + A * Real.log (1 / δ) ≤ C_real * δ ^ (-η) := by
    calc
      B + A * Real.log (1 / δ)
        ≤ B * δ ^ (-η) + C_log * δ ^ (-η) := by gcongr
      _ = (B + C_log) * δ ^ (-η) := by ring
      _ = C_real * δ ^ (-η) := by rfl
  have h_ge_one : 1 / δ ≥ 1 := by
    have h9 : 1 / δ ≥ 1 / 1 := by gcongr
    simpa using h9
  have h5 : 0 ≤ B + A * Real.log (1 / δ) := by
    have h6 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg h_ge_one
    have h7 : 0 ≤ A * Real.log (1 / δ) := by positivity
    linarith
  have h6 : ENNReal.ofReal (B + A * Real.log (1 / δ)) ≤
      ENNReal.ofReal (C_real * δ ^ (-η)) :=
    ENNReal.ofReal_le_ofReal h1
  have h8 : ENNReal.ofReal (C_real * δ ^ (-η)) =
      C * Kakeya.realRpowENN δ (-η) := by
    simp [C, Kakeya.realRpowENN, ENNReal.ofReal_mul hC_nonneg]
    <;> rfl
  rw [h8] at h6
  exact h6

end Kakeya.Streamlined
