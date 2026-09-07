module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Incidence double-counting lemmas for Proposition 2

Provides `countContained` and the key double-counting identities:
- Total incidence lower/upper bounds
- Per-coarse-tube incidence lower bound
- Sum interchange

Whiteprint node: InductionOnScales/Proposition2/IncidenceBound
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Number of fine tubes in `F` geometrically contained in coarse tube `U`. -/
def countContained {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (U : DyadicTube m) : ℕ :=
  (F.filter (fun (T : DyadicTube n) => T.toSet ⊆ U.toSet)).card

/-- `countContained` is bounded by the size of the fine family. -/
lemma countContained_le_card {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n)) (U : DyadicTube m) :
    countContained hnm F U ≤ F.card := by
  have h : (F.filter (fun (T : DyadicTube n) => T.toSet ⊆ U.toSet)).card ≤ F.card :=
    Finset.card_filter_le F _
  exact h

/-- Sum interchange for contained-tube counts. -/
lemma countContained_sum_comm {n m : ℕ} (hnm : m ≤ n)
    {P : Type*} [DecidableEq P]
    (points : Finset P) (coarseTubes : Finset (DyadicTube m))
    (fineFamily : P → Finset (DyadicTube n)) :
    ∑ U ∈ coarseTubes, ∑ p ∈ points, countContained hnm (fineFamily p) U =
    ∑ p ∈ points, ∑ U ∈ coarseTubes, countContained hnm (fineFamily p) U := by
  rw [Finset.sum_comm]

/-- Lower bound: total incidences ≥ m₁ * Σ |coarseFamily p|. -/
lemma totalIncidences_lower_bound {n m : ℕ} (hnm : m ≤ n)
    {P : Type*} [DecidableEq P]
    (points : Finset P)
    (fineFamily : P → Finset (DyadicTube n))
    (coarseFamily : P → Finset (DyadicTube m))
    (m₁ : ℕ)
    (h : ∀ p ∈ points, ∀ U ∈ coarseFamily p,
      countContained hnm (fineFamily p) U ≥ m₁) :
    ∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≥
    m₁ * ∑ p ∈ points, (coarseFamily p).card := by
  have h1 : ∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≥
      ∑ p ∈ points, ∑ U ∈ coarseFamily p, m₁ := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro U hU
    exact h p hp U hU
  have h2 : ∑ p ∈ points, ∑ U ∈ coarseFamily p, m₁ =
      ∑ p ∈ points, (m₁ * (coarseFamily p).card) := by
    apply Finset.sum_congr rfl
    intro p _
    simp [Finset.sum_const]
    <;> ring
  have h3 : ∑ p ∈ points, (m₁ * (coarseFamily p).card) =
      m₁ * ∑ p ∈ points, (coarseFamily p).card := by
    rw [Finset.mul_sum] <;> ring
  rw [h2, h3] at h1
  exact h1

/-- Upper bound: total incidences ≤ M * |points|, using uniqueness of coarse
ancestor. Each fine tube is contained in at most one coarse tube, so it is
counted at most once across all U in coarseFamily p. -/
lemma totalIncidences_upper_bound {n m : ℕ} (hnm : m ≤ n)
    {P : Type*} [DecidableEq P]
    (points : Finset P)
    (fineFamily : P → Finset (DyadicTube n))
    (coarseFamily : P → Finset (DyadicTube m))
    (M : ℕ)
    (h_size : ∀ p ∈ points, (fineFamily p).card = M)
    (h_unique : ∀ (T : DyadicTube n) (U V : DyadicTube m),
      T.toSet ⊆ U.toSet → T.toSet ⊆ V.toSet → U = V) :
    ∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≤
    M * points.card := by
  have h_per_p : ∀ p ∈ points,
      ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≤ (fineFamily p).card := by
    intro p hp
    let filterU (U : DyadicTube m) : Finset (DyadicTube n) :=
      (fineFamily p).filter (fun (T : DyadicTube n) => T.toSet ⊆ U.toSet)
    have h_disj : ∀ U ∈ coarseFamily p, ∀ V ∈ coarseFamily p, U ≠ V →
        Disjoint (filterU U) (filterU V) := by
      intro U _ V _ hne
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have h1 : T.toSet ⊆ U.toSet := (Finset.mem_filter.mp hT1).2
      have h2 : T.toSet ⊆ V.toSet := (Finset.mem_filter.mp hT2).2
      have h3 : U = V := h_unique T U V h1 h2
      exact hne h3
    have h_union : Finset.biUnion (coarseFamily p) filterU ⊆ fineFamily p := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨U, _, hTU⟩
      exact (Finset.mem_filter.mp hTU).1
    have h_sum : ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U =
        (Finset.biUnion (coarseFamily p) filterU).card := by
      rw [Finset.card_biUnion h_disj] <;> rfl
    rw [h_sum]
    exact Finset.card_le_card h_union
  have h4 : ∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≤
      ∑ p ∈ points, (fineFamily p).card := Finset.sum_le_sum h_per_p
  have h5 : ∑ p ∈ points, (fineFamily p).card = ∑ p ∈ points, M := by
    apply Finset.sum_congr rfl
    intro p hp
    exact h_size p hp
  have h6 : ∑ p ∈ points, M = M * points.card := by
    simp [Finset.sum_const] <;> ring
  rw [h5, h6] at h4
  exact h4

/-- Per-coarse-tube lower bound: for each U ∈ TΔ, the sum over p of
countContained(fineFamily p, U) ≥ L * m₁. -/
lemma perCoarseIncidence_lower_bound {n m : ℕ} (hnm : m ≤ n)
    {P : Type*} [DecidableEq P]
    (points : Finset P)
    (fineFamily : P → Finset (DyadicTube n))
    (coarseFamily : P → Finset (DyadicTube m))
    (TΔ : Finset (DyadicTube m))
    (L m₁ : ℕ)
    (h_pop : ∀ U ∈ TΔ, (points.filter (fun p => U ∈ coarseFamily p)).card ≥ L)
    (h_per : ∀ p ∈ points, ∀ U ∈ coarseFamily p,
      countContained hnm (fineFamily p) U ≥ m₁) :
    ∀ U ∈ TΔ,
      ∑ p ∈ points, countContained hnm (fineFamily p) U ≥ L * m₁ := by
  intro U hU
  let P_U := points.filter (fun p => U ∈ coarseFamily p)
  have hP_U_card : P_U.card ≥ L := h_pop U hU
  have h_main : ∑ p ∈ P_U, countContained hnm (fineFamily p) U ≥ P_U.card * m₁ := by
    have h7 : ∑ p ∈ P_U, countContained hnm (fineFamily p) U ≥ ∑ p ∈ P_U, m₁ := by
      apply Finset.sum_le_sum
      intro p hp
      have h_in : U ∈ coarseFamily p := (Finset.mem_filter.mp hp).2
      exact h_per p (Finset.mem_filter.mp hp).1 U h_in
    have h8 : ∑ p ∈ P_U, m₁ = P_U.card * m₁ := by
      simp [Finset.sum_const] <;> ring
    rw [h8] at h7
    exact h7
  have h_zeros : ∑ p ∈ points, countContained hnm (fineFamily p) U ≥
      ∑ p ∈ P_U, countContained hnm (fineFamily p) U := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact (Finset.mem_filter.mp hp).1
    · intro _ _ _
      exact Nat.zero_le _
  have h9 : ∑ p ∈ points, countContained hnm (fineFamily p) U ≥ P_U.card * m₁ := by
    calc ∑ p ∈ points, countContained hnm (fineFamily p) U
      ≥ ∑ p ∈ P_U, countContained hnm (fineFamily p) U := h_zeros
    _ ≥ P_U.card * m₁ := h_main
  have h10 : (P_U.card : ℕ) * m₁ ≥ L * m₁ := by
    exact mul_le_mul_of_nonneg_right hP_U_card (by positivity)
  exact le_trans h10 h9

/-- Combined double-counting theorem: given the hypotheses, both the total
incidence bound and the per-coarse-tube bound hold simultaneously. -/
theorem incidence_double_counting {n m : ℕ} (hnm : m ≤ n)
    {P : Type*} [DecidableEq P]
    (points : Finset P)
    (fineFamily : P → Finset (DyadicTube n))
    (coarseFamily : P → Finset (DyadicTube m))
    (TΔ : Finset (DyadicTube m))
    (M L m₁ : ℕ)
    (h_size : ∀ p ∈ points, (fineFamily p).card = M)
    (h_per : ∀ p ∈ points, ∀ U ∈ coarseFamily p,
      countContained hnm (fineFamily p) U ≥ m₁)
    (h_pop : ∀ U ∈ TΔ, (points.filter (fun p => U ∈ coarseFamily p)).card ≥ L)
    (h_unique : ∀ (T : DyadicTube n) (U V : DyadicTube m),
      T.toSet ⊆ U.toSet → T.toSet ⊆ V.toSet → U = V) :
    (∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≥
       m₁ * ∑ p ∈ points, (coarseFamily p).card) ∧
    (∑ p ∈ points, ∑ U ∈ coarseFamily p, countContained hnm (fineFamily p) U ≤
       M * points.card) ∧
    (∀ U ∈ TΔ, ∑ p ∈ points, countContained hnm (fineFamily p) U ≥ L * m₁) := by
  exact ⟨
    totalIncidences_lower_bound hnm points fineFamily coarseFamily m₁ h_per,
    totalIncidences_upper_bound hnm points fineFamily coarseFamily M h_size h_unique,
    perCoarseIncidence_lower_bound hnm points fineFamily coarseFamily TΔ L m₁ h_pop h_per
  ⟩

-- ============================================================================
-- Uniqueness of containing coarse tube and sum identity
-- ============================================================================

/-- A fine tube can be geometrically contained in at most one coarse tube.
This follows because the parameter rectangles of distinct coarse tubes are
disjoint, and tube containment is equivalent to parameter-rectangle nesting. -/
lemma unique_containing_coarse_tube {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (U V : DyadicTube m)
    (h1 : T.toSet ⊆ U.toSet) (h2 : T.toSet ⊆ V.toSet) : U = V := by
  let f : ℕ := coarseRefinementFactor n m
  have hf_pos : 0 < f := InductionOnScales.coarseRefinementFactor_pos n m
  have hf_pos' : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf_pos
  have hU := (InductionOnScales.tube_containment_iff hnm T U).mp h1
  have hV := (InductionOnScales.tube_containment_iff hnm T V).mp h2
  have hUa1 : (U.a : ℤ) * (f : ℤ) ≤ T.a := hU.1
  have hUa2 : T.a < (U.a + 1) * (f : ℤ) := by linarith
  have hVa1 : (V.a : ℤ) * (f : ℤ) ≤ T.a := hV.1
  have hVa2 : T.a < (V.a + 1) * (f : ℤ) := by linarith
  have h_k_spec := InductionOnScales.coarseParentIndex_spec n m hnm T.a
  let k := coarseParentIndex n m T.a
  have hk1 : (k : ℤ) * (f : ℤ) ≤ T.a := h_k_spec.1
  have hk2 : T.a < (k + 1) * (f : ℤ) := h_k_spec.2
  have hUa : U.a = k := by
    have h1 : U.a ≤ k := by
      have h : (U.a : ℤ) * (f : ℤ) < (k + 1) * (f : ℤ) := hUa1.trans_lt hk2
      nlinarith
    have h2 : k ≤ U.a := by
      have h : (k : ℤ) * (f : ℤ) < (U.a + 1) * (f : ℤ) := hk1.trans_lt hUa2
      nlinarith
    omega
  have hVa : V.a = k := by
    have h1 : V.a ≤ k := by
      have h : (V.a : ℤ) * (f : ℤ) < (k + 1) * (f : ℤ) := hVa1.trans_lt hk2
      nlinarith
    have h2 : k ≤ V.a := by
      have h : (k : ℤ) * (f : ℤ) < (V.a + 1) * (f : ℤ) := hk1.trans_lt hVa2
      nlinarith
    omega
  have h_a : U.a = V.a := by rw [hUa, hVa]
  have hUb1 : (U.b : ℤ) * (f : ℤ) ≤ T.b := hU.2.2.1
  have hUb2 : T.b < (U.b + 1) * (f : ℤ) := by linarith
  have hVb1 : (V.b : ℤ) * (f : ℤ) ≤ T.b := hV.2.2.1
  have hVb2 : T.b < (V.b + 1) * (f : ℤ) := by linarith
  have h_k_spec_b := InductionOnScales.coarseParentIndex_spec n m hnm T.b
  let kb := coarseParentIndex n m T.b
  have hkb1 : (kb : ℤ) * (f : ℤ) ≤ T.b := h_k_spec_b.1
  have hkb2 : T.b < (kb + 1) * (f : ℤ) := h_k_spec_b.2
  have hUb : U.b = kb := by
    have h1 : U.b ≤ kb := by
      have h : (U.b : ℤ) * (f : ℤ) < (kb + 1) * (f : ℤ) := hUb1.trans_lt hkb2
      nlinarith
    have h2 : kb ≤ U.b := by
      have h : (kb : ℤ) * (f : ℤ) < (U.b + 1) * (f : ℤ) := hkb1.trans_lt hUb2
      nlinarith
    omega
  have hVb : V.b = kb := by
    have h1 : V.b ≤ kb := by
      have h : (V.b : ℤ) * (f : ℤ) < (kb + 1) * (f : ℤ) := hVb1.trans_lt hkb2
      nlinarith
    have h2 : kb ≤ V.b := by
      have h : (kb : ℤ) * (f : ℤ) < (V.b + 1) * (f : ℤ) := hkb1.trans_lt hVb2
      nlinarith
    omega
  have h_b : U.b = V.b := by rw [hUb, hVb]
  cases U; cases V; simp_all [DyadicTube.mk.injEq] <;> omega

/-- Sum identity: if `TΔ` covers `F` (every fine tube is contained in some
coarse tube in `TΔ`), then `Σ_{U ∈ TΔ} countContained(F, U) = |F|`.

This uses uniqueness of the containing coarse tube: each fine tube is counted
exactly once in the sum. -/
lemma sum_filter_ancestor {n m : ℕ} (hnm : m ≤ n)
    (F : Finset (DyadicTube n))
    (TΔ : Finset (DyadicTube m))
    (h_cover : ∀ T ∈ F, ∃ U ∈ TΔ, T.toSet ⊆ U.toSet) :
    ∑ U ∈ TΔ, countContained hnm F U = F.card := by
  let fiber (U : DyadicTube m) : Finset (DyadicTube n) :=
    F.filter (fun (T : DyadicTube n) => T.toSet ⊆ U.toSet)
  have h_disj : ∀ U ∈ TΔ, ∀ V ∈ TΔ, U ≠ V → Disjoint (fiber U) (fiber V) := by
    intro U _ V _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h1 : T.toSet ⊆ U.toSet := (Finset.mem_filter.mp hT1).2
    have h2 : T.toSet ⊆ V.toSet := (Finset.mem_filter.mp hT2).2
    have h3 : U = V := unique_containing_coarse_tube hnm T U V h1 h2
    exact hne h3
  have h_union : Finset.biUnion TΔ fiber = F := by
    ext T
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨U, _, hT⟩
      exact (Finset.mem_filter.mp hT).1
    · intro hT
      rcases h_cover T hT with ⟨U, hU, hcont⟩
      exact ⟨U, hU, Finset.mem_filter.mpr ⟨hT, hcont⟩⟩
  have h_sum : ∑ U ∈ TΔ, (fiber U).card = (Finset.biUnion TΔ fiber).card := by
    rw [Finset.card_biUnion h_disj]
    <;> rfl
  have h_main : ∑ U ∈ TΔ, countContained hnm F U = ∑ U ∈ TΔ, (fiber U).card := by
    apply Finset.sum_congr rfl
    intro U _
    rfl
  rw [h_main, h_sum, h_union]

end
