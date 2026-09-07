module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.TubePackets
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Coarse Phase Helper Lemmas
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales.CoarsePhaseHelpers

/-- Helper: if a dyadic square p is contained in unitSquare, its index bounds
satisfy `0 ≤ p.i` and `p.i < 2^n` (and similarly for j). -/
lemma dyadic_square_in_unitSquare_bounds {n : ℕ} (p : DyadicSquare n)
    (h : p.toSet ⊆ unitSquare) :
    0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_inv : dyadicDelta n = 1 / (2 ^ n : ℝ) := dyadicDelta_eq_inv n
  -- x-projection: pick y = p.j * δ, then (p.i*δ, p.j*δ) ∈ p.toSet
  let x0 : ℝ := (p.i : ℝ) * dyadicDelta n
  let y0 : ℝ := (p.j : ℝ) * dyadicDelta n
  have h_p1 : (x0, y0) ∈ p.toSet := by
    simp [DyadicSquare.toSet, x0, y0, hδ_pos] <;> norm_num <;> linarith
  have h_u1 : (x0, y0) ∈ unitSquare := h h_p1
  have h_x0_nonneg : 0 ≤ x0 := (Set.mem_prod.mp h_u1).1.1
  have h_x0_lt_one : x0 < 1 := (Set.mem_prod.mp h_u1).1.2
  have h_y0_nonneg : 0 ≤ y0 := (Set.mem_prod.mp h_u1).2.1
  -- For upper bound, pick x close to (p.i+1)*δ and y = p.j*δ
  -- Actually use (p.i+1)*δ - δ/2 = (p.i + 1/2)*δ
  let x1 : ℝ := ((p.i : ℝ) + 1 / 2) * dyadicDelta n
  have h_x1_in : x1 ∈ Set.Ico ((p.i : ℝ) * dyadicDelta n) (((p.i + 1 : ℝ)) * dyadicDelta n) := by
    constructor <;> simp [x1, hδ_pos] <;> linarith
  have h_p2 : (x1, y0) ∈ p.toSet := by
    simp [DyadicSquare.toSet, h_x1_in, y0, hδ_pos] <;> norm_num <;> linarith
  have h_u2 : (x1, y0) ∈ unitSquare := h h_p2
  have h_x1_lt_one : x1 < 1 := (Set.mem_prod.mp h_u2).1.2
  -- Similarly for y
  let y1 : ℝ := ((p.j : ℝ) + 1 / 2) * dyadicDelta n
  have h_y1_in : y1 ∈ Set.Ico ((p.j : ℝ) * dyadicDelta n) (((p.j + 1 : ℝ)) * dyadicDelta n) := by
    constructor <;> simp [y1, hδ_pos] <;> linarith
  have h_p3 : (x0, y1) ∈ p.toSet := by
    simp [DyadicSquare.toSet, h_y1_in, x0, hδ_pos] <;> norm_num <;> linarith
  have h_u3 : (x0, y1) ∈ unitSquare := h h_p3
  have h_y1_lt_one : y1 < 1 := (Set.mem_prod.mp h_u3).2.2
  -- Derive integer bounds
  have h_pi_nonneg : 0 ≤ p.i := by
    have h : 0 ≤ (p.i : ℝ) * dyadicDelta n := h_x0_nonneg
    have hδ : 0 < dyadicDelta n := hδ_pos
    have h' : 0 ≤ (p.i : ℝ) := by nlinarith
    exact_mod_cast h'
  have h_pi_lt : p.i < (2 ^ n : ℤ) := by
    have h : ((p.i : ℝ) + 1 / 2) * dyadicDelta n < 1 := h_x1_lt_one
    rw [hδ_inv] at h
    have h' : (p.i : ℝ) + 1 / 2 < (2 ^ n : ℝ) := by
      field_simp at h <;> nlinarith
    have h'' : (p.i : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h''
  have h_pj_nonneg : 0 ≤ p.j := by
    have h : 0 ≤ (p.j : ℝ) * dyadicDelta n := h_y0_nonneg
    have hδ : 0 < dyadicDelta n := hδ_pos
    have h' : 0 ≤ (p.j : ℝ) := by nlinarith
    exact_mod_cast h'
  have h_pj_lt : p.j < (2 ^ n : ℤ) := by
    have h : ((p.j : ℝ) + 1 / 2) * dyadicDelta n < 1 := h_y1_lt_one
    rw [hδ_inv] at h
    have h' : (p.j : ℝ) + 1 / 2 < (2 ^ n : ℝ) := by
      field_simp at h <;> nlinarith
    have h'' : (p.j : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h''
  exact ⟨h_pi_nonneg, h_pi_lt, h_pj_nonneg, h_pj_lt⟩

/-- If `p.toSet ⊆ unitSquare`, then `(containingSquare hnm p).toSet ⊆ unitSquare`. -/
lemma coarse_square_bounded {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (h : p.toSet ⊆ unitSquare) :
    (containingSquare hnm p).toSet ⊆ unitSquare := by
  let Q := containingSquare hnm p
  let R : ℕ := coarseRefinementFactor n m
  have hR_pos : 0 < (R : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
  have hδm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h_bounds := dyadic_square_in_unitSquare_bounds p h

  -- Q.i = floor(p.i / R), so 0 ≤ p.i implies 0 ≤ Q.i
  have hQi_nonneg : 0 ≤ Q.i := by
    have h1 : 0 ≤ (p.i : ℝ) / (R : ℝ) := by
      apply div_nonneg
      · exact_mod_cast h_bounds.1
      · exact Nat.cast_nonneg R
    have h2 : (0 : ℤ) ≤ Q.i := by
      have h3 : Q.i = Int.floor ((p.i : ℝ) / (R : ℝ)) := by rfl
      rw [h3]
      exact Int.floor_nonneg.mpr h1
    exact h2

  -- p.i < 2^n implies Q.i < 2^m
  have hQi_lt : Q.i < (2 ^ m : ℤ) := by
    have hR_eq : (R : ℝ) = (2 ^ (n - m) : ℝ) := by
      simp [R, coarseRefinementFactor] <;> norm_cast
    have h1 : (p.i : ℝ) / (R : ℝ) < (2 ^ m : ℝ) := by
      have h2 : (p.i : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_bounds.2.1
      have h3 : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
        simp [Nat.cast_sub hnm] <;> ring
      have h4 : (2 ^ n : ℝ) = (2 ^ m : ℝ) * (2 ^ (n - m) : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [h3, Real.rpow_add] <;> norm_num
      rw [hR_eq]
      rw [h4] at h2
      field_simp <;> nlinarith
    have h5 : (Q.i : ℝ) < (2 ^ m : ℝ) := by
      have h6 : (Q.i : ℝ) = Int.floor ((p.i : ℝ) / (R : ℝ)) := by rfl
      rw [h6]
      have h7 : (Int.floor ((p.i : ℝ) / (R : ℝ)) : ℝ) ≤ (p.i : ℝ) / (R : ℝ) := Int.floor_le _
      linarith
    exact_mod_cast h5

  -- Same for Q.j
  have hQj_nonneg : 0 ≤ Q.j := by
    have h1 : 0 ≤ (p.j : ℝ) / (R : ℝ) := by
      apply div_nonneg
      · exact_mod_cast h_bounds.2.2.1
      · exact Nat.cast_nonneg R
    have h2 : (0 : ℤ) ≤ Q.j := by
      have h3 : Q.j = Int.floor ((p.j : ℝ) / (R : ℝ)) := by rfl
      rw [h3]
      exact Int.floor_nonneg.mpr h1
    exact h2

  have hQj_lt : Q.j < (2 ^ m : ℤ) := by
    have hR_eq : (R : ℝ) = (2 ^ (n - m) : ℝ) := by
      simp [R, coarseRefinementFactor] <;> norm_cast
    have h1 : (p.j : ℝ) / (R : ℝ) < (2 ^ m : ℝ) := by
      have h2 : (p.j : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_bounds.2.2.2
      have h3 : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
        simp [Nat.cast_sub hnm] <;> ring
      have h4 : (2 ^ n : ℝ) = (2 ^ m : ℝ) * (2 ^ (n - m) : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [h3, Real.rpow_add] <;> norm_num
      rw [hR_eq]
      rw [h4] at h2
      field_simp <;> nlinarith
    have h5 : (Q.j : ℝ) < (2 ^ m : ℝ) := by
      have h6 : (Q.j : ℝ) = Int.floor ((p.j : ℝ) / (R : ℝ)) := by rfl
      rw [h6]
      have h7 : (Int.floor ((p.j : ℝ) / (R : ℝ)) : ℝ) ≤ (p.j : ℝ) / (R : ℝ) := Int.floor_le _
      linarith
    exact_mod_cast h5

  -- Conclude Q.toSet ⊆ unitSquare
  intro x hx
  have hx1 : x.1 ∈ Set.Ico ((Q.i : ℝ) * dyadicDelta m) (((Q.i + 1 : ℝ)) * dyadicDelta m) :=
    (Set.mem_prod.mp hx).1
  have hx2 : x.2 ∈ Set.Ico ((Q.j : ℝ) * dyadicDelta m) (((Q.j + 1 : ℝ)) * dyadicDelta m) :=
    (Set.mem_prod.mp hx).2
  have hδ_inv : dyadicDelta m = 1 / (2 ^ m : ℝ) := dyadicDelta_eq_inv m
  have hQi1 : (0 : ℝ) ≤ (Q.i : ℝ) * dyadicDelta m := by
    have h : 0 ≤ (Q.i : ℝ) := by exact_mod_cast hQi_nonneg
    exact mul_nonneg h (le_of_lt hδm_pos)
  have hQi2 : ((Q.i + 1 : ℝ)) * dyadicDelta m ≤ 1 := by
    have h : (Q.i + 1 : ℤ) ≤ (2 ^ m : ℤ) := by
      have h' : Q.i < (2 ^ m : ℤ) := hQi_lt
      omega
    have h' : (Q.i + 1 : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast h
    rw [hδ_inv]
    have h9 : (Q.i + 1 : ℝ) * (1 / (2 ^ m : ℝ)) ≤ (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) := by gcongr
    have h10 : (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) = 1 := by field_simp <;> ring
    linarith
  have hQj1 : (0 : ℝ) ≤ (Q.j : ℝ) * dyadicDelta m := by
    have h : 0 ≤ (Q.j : ℝ) := by exact_mod_cast hQj_nonneg
    exact mul_nonneg h (le_of_lt hδm_pos)
  have hQj2 : ((Q.j + 1 : ℝ)) * dyadicDelta m ≤ 1 := by
    have h : (Q.j + 1 : ℤ) ≤ (2 ^ m : ℤ) := by
      have h' : Q.j < (2 ^ m : ℤ) := hQj_lt
      omega
    have h' : (Q.j + 1 : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast h
    rw [hδ_inv]
    have h9 : (Q.j + 1 : ℝ) * (1 / (2 ^ m : ℝ)) ≤ (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) := by gcongr
    have h10 : (2 ^ m : ℝ) * (1 / (2 ^ m : ℝ)) = 1 := by field_simp <;> ring
    linarith
  simp only [unitSquare, Set.mem_prod]
  exact ⟨⟨by linarith [hx1.1], by linarith [hx1.2, hQi2]⟩,
    ⟨by linarith [hx2.1], by linarith [hx2.2, hQj2]⟩⟩

/-- A fine tube is geometrically contained in its coarse ancestor. -/
lemma coarse_ancestor_containment {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) :
    T.toSet ⊆ (deprecatedCoordinatewiseAncestor hnm T).toSet :=
  fine_tube_in_coarse_ancestor hnm T

/-- If U is in the union of per-point coarse families restricted to Q, then there
exists a point p ∈ P contained in Q such that U ∈ coarseFamily p. -/
lemma coarse_family_union_per_Q {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (coarseFamily : DyadicSquare n → Finset (DyadicTube m))
    (Q : DyadicSquare m)
    (U : DyadicTube m)
    (hU : U ∈ (P.filter (fun p => squareContained hnm p Q)).biUnion coarseFamily) :
    ∃ (p : DyadicSquare n), p ∈ P ∧ squareContained hnm p Q ∧ U ∈ coarseFamily p := by
  rcases Finset.mem_biUnion.mp hU with ⟨p, hp_filter, hUp⟩
  have hp_in_P : p ∈ P := (Finset.mem_filter.mp hp_filter).1
  have hp_contained : squareContained hnm p Q := (Finset.mem_filter.mp hp_filter).2
  exact ⟨p, hp_in_P, hp_contained, hUp⟩

/-- Given a nonempty finset `QSet` and a family `fam`, let MΔ be the maximum
cardinality. Then every family has size ≤ MΔ, and some Q₀ attains the maximum. -/
lemma max_family_size {α : Type*} [DecidableEq α] {m : ℕ}
    (QSet : Finset α) (hQSet_nonempty : QSet.Nonempty)
    (fam : α → Finset (DyadicTube m)) :
    ∃ (MΔ : ℕ), (∀ Q ∈ QSet, (fam Q).card ≤ MΔ) ∧
      ∃ (Q₀ : α), Q₀ ∈ QSet ∧ (fam Q₀).card = MΔ := by
  let MΔ := QSet.sup (fun Q => (fam Q).card)
  have h1 : ∀ Q ∈ QSet, (fam Q).card ≤ MΔ := by
    intro Q hQ
    exact Finset.le_sup (f := fun Q => (fam Q).card) hQ
  have h2 : ∃ Q₀ ∈ QSet, (fam Q₀).card = MΔ := by
    rcases Finset.exists_mem_eq_sup QSet hQSet_nonempty (fun Q => (fam Q).card) with ⟨Q₀, hQ₀, h_eq⟩
    exact ⟨Q₀, hQ₀, h_eq.symm⟩
  exact ⟨MΔ, h1, h2⟩

/-- If `bandTubes p` is nonempty and every coarse ancestor of a bandTube is in
`coarseTubes`, then `retained p` (bandTubes filtered by coarse ancestor membership)
is nonempty. -/
lemma retained_tubes_nonempty {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n)
    (bandTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (h_band_nonempty : bandTubes.Nonempty)
    (h_coverage : ∀ T ∈ bandTubes, deprecatedCoordinatewiseAncestor hnm T ∈ coarseTubes) :
    (bandTubes.filter (fun T => deprecatedCoordinatewiseAncestor hnm T ∈ coarseTubes)).Nonempty := by
  rcases h_band_nonempty with ⟨T, hT⟩
  have h_anc : deprecatedCoordinatewiseAncestor hnm T ∈ coarseTubes := h_coverage T hT
  exact ⟨T, Finset.mem_filter.mpr ⟨hT, h_anc⟩⟩

/-- If each `fam Q` is a subset of `coarseTubes`, then their biUnion is too. -/
lemma coarseConfig_tubes_union {α : Type*} [DecidableEq α] {m : ℕ}
    (QSet : Finset α) (fam : α → Finset (DyadicTube m))
    (coarseTubes : Finset (DyadicTube m))
    (h : ∀ Q ∈ QSet, fam Q ⊆ coarseTubes) :
    (QSet.biUnion fam) ⊆ coarseTubes := by
  intro U hU
  rcases Finset.mem_biUnion.mp hU with ⟨Q, hQ, hUQ⟩
  exact h Q hQ hUQ

/-- If a family of finsets is pairwise δ-separated and each member is an SSet with
the same constant C, then their biUnion is also an SSet with constant C. -/
lemma union_disjoint_sset {n : ℕ} {s C : ℝ} {α : Type*} [DecidableEq α]
    (idx : Finset α)
    (fam : α → Finset (DyadicTube n))
    (h_sset : ∀ i ∈ idx, IsFiniteTubeSSet s C (fam i))
    (h_disjoint : ∀ i ∈ idx, ∀ j ∈ idx, i ≠ j →
      ∀ T ∈ fam i, ∀ U ∈ fam j, dyadicDelta n ≤ tubeParamDist T U)
    (h_nonempty : idx.Nonempty) :
    IsFiniteTubeSSet s C (idx.biUnion fam) := by
  let U := idx.biUnion fam
  have h_fam_disjoint : ∀ i ∈ idx, ∀ j ∈ idx, i ≠ j → Disjoint (fam i) (fam j) := by
    intro i hi j hj hne
    rw [Finset.disjoint_left]
    intro T hTi hTj
    have h_sep : dyadicDelta n ≤ tubeParamDist T T := h_disjoint i hi j hj hne T hTi T hTj
    have h_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h_zero : tubeParamDist T T = 0 := by simp [tubeParamDist] <;> norm_num
    rw [h_zero] at h_sep
    linarith
  have hU_nonempty : U.Nonempty := by
    rcases h_nonempty with ⟨i, hi⟩
    have h_fam_nonempty : (fam i).Nonempty := (h_sset i hi).1
    rcases h_fam_nonempty with ⟨T, hT⟩
    exact ⟨T, Finset.mem_biUnion.mpr ⟨i, hi, hT⟩⟩
  let i0 := Classical.choose h_nonempty
  have hi0 : i0 ∈ idx := Classical.choose_spec h_nonempty
  have hC_one : 1 ≤ C := (h_sset i0 hi0).2.1
  have hs : 0 ≤ s := (h_sset i0 hi0).2.2.1
  have h_card_union : (U.card : ℝ) = ∑ i ∈ idx, ((fam i).card : ℝ) := by
    rw [Finset.card_biUnion h_fam_disjoint] <;> norm_cast
  refine ⟨hU_nonempty, hC_one, hs, ?_, ?_⟩
  · intro T hT V hV hne
    rcases Finset.mem_biUnion.mp hT with ⟨i, hi, hTi⟩
    rcases Finset.mem_biUnion.mp hV with ⟨j, hj, hVj⟩
    by_cases h_ij : i = j
    · subst h_ij
      exact (h_sset i hi).2.2.2.1 T hTi V hVj hne
    · exact h_disjoint i hi j hj h_ij T hTi V hVj
  · intro center r hr
    let filter_fam (i : α) := (fam i).filter (fun T => tubeParamDist T center ≤ r)
    have h_disj_filter : ∀ i ∈ idx, ∀ j ∈ idx, i ≠ j → Disjoint (filter_fam i) (filter_fam j) := by
      intro i hi j hj hne
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (h_fam_disjoint i hi j hj hne)
    have h1 : U.filter (fun T => tubeParamDist T center ≤ r) = idx.biUnion filter_fam := by
      ext T; simp only [Finset.mem_filter, Finset.mem_biUnion] <;> aesop
    rw [h1]
    have h2 : ((idx.biUnion filter_fam).card : ℝ) = ∑ i ∈ idx, ((filter_fam i).card : ℝ) := by
      rw [Finset.card_biUnion h_disj_filter] <;> norm_cast
    rw [h2]
    have h3 : ∑ i ∈ idx, ((filter_fam i).card : ℝ) ≤
        ∑ i ∈ idx, (C * Real.rpow r s * ((fam i).card : ℝ)) := by
      apply Finset.sum_le_sum; intro i hi; exact (h_sset i hi).2.2.2.2 center r hr
    have h4 : ∑ i ∈ idx, (C * Real.rpow r s * ((fam i).card : ℝ)) =
        C * Real.rpow r s * ∑ i ∈ idx, ((fam i).card : ℝ) := by
      simp [Finset.mul_sum] <;> ring
    rw [h4] at h3
    rw [h_card_union] at * <;> exact h3

/-- Restrict a NiceConfiguration to points in a single coarse square Q and obtain
all hypotheses needed for `proposition2_optimized`. -/
lemma prop2_per_Q_restriction
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (Q : DyadicSquare m)
    (hQ_nonempty : (config.points.filter (fun p => squareContained hnm p Q)).Nonempty) :
    ∃ (P_Q : Finset (DyadicSquare n))
      (tubeFamily_Q : (p : DyadicSquare n) → p ∈ P_Q → Finset (DyadicTube n)),
      P_Q = config.points.filter (fun p => squareContained hnm p Q) ∧
      (∀ p hp, IsFiniteTubeSSet s C₁ (tubeFamily_Q p hp)) ∧
      (∀ p hp, (tubeFamily_Q p hp).card = M) ∧
      (∀ p hp T, T ∈ tubeFamily_Q p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ tubeFamily_Q p hp → T.IsInAllowedParameterStrip) ∧
      (∀ p ∈ P_Q, p.toSet ⊆ unitSquare) ∧
      P_Q.Nonempty := by
  let P_Q := config.points.filter (fun p => squareContained hnm p Q)
  let tubeFamily_Q : (p : DyadicSquare n) → p ∈ P_Q → Finset (DyadicTube n) :=
    fun p hp => config.tubeFamily p ((Finset.mem_filter.mp hp).1)
  refine ⟨P_Q, tubeFamily_Q, rfl, ?_⟩
  constructor
  · intro p hp; exact config.h_sset p ((Finset.mem_filter.mp hp).1)
  constructor
  · intro p hp; exact config.h_size p ((Finset.mem_filter.mp hp).1)
  constructor
  · intro p hp T hT; exact config.h_incidence p ((Finset.mem_filter.mp hp).1) T hT
  constructor
  · intro p hp T hT
    exact config.h_tube_parameters T (config.h_subset p ((Finset.mem_filter.mp hp).1) hT)
  constructor
  · intro p hp; exact config.h_bounded p ((Finset.mem_filter.mp hp).1)
  · exact hQ_nonempty

end CoarsePhaseHelpers

end InductionOnScales
