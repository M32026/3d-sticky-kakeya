module

public import MyLeanRepo.InductionOnScales.Definitions

@[expose] public section

/-!
# Slope cells and parameter-space separation

Lemmas about `localSlopeCellIndex` and greedy selection of separated
subsets, used in the proof of OS Proposition 5.1 (induction on scales).

## Main results

- `localSlopeCellIndex_eq_ediv`: `localSlopeCellIndex m a = a / 2^m`
- `localSlopeCellIndex_bounds`: cell index bounds the original index
- `same_slope_cell_slopes_close`: same cell ⇒ slopes within `δ/Δ`
- `exists_c_separated_subset`: every finite `Finset ℤ` has a `c`-separated
  subset of size at least `|B| / (c + 1)` (OS Lemma 4, discrete version)

## Whiteprint node
`slope_cell_preservation` under `InductionOnScales/SlopeCells/`.
-/

open scoped BigOperators

namespace InductionOnScales

section SlopeCellLemmas

/-- `localSlopeCellIndex m a` equals integer division `a / 2^m`. -/
lemma localSlopeCellIndex_eq_ediv (m : ℕ) (a : ℤ) :
    localSlopeCellIndex m a = a / (2 ^ m : ℤ) := by
  simp only [localSlopeCellIndex]
  rw [Int.floor_div_natCast (a : ℝ) (2 ^ m)]
  <;> simp

/-- Bounding specification for `localSlopeCellIndex`. -/
lemma localSlopeCellIndex_bounds (m : ℕ) (a : ℤ) :
    (localSlopeCellIndex m a : ℝ) * ((2 ^ m : ℕ) : ℝ) ≤ (a : ℝ) ∧
    (a : ℝ) < ((localSlopeCellIndex m a : ℝ) + 1) * ((2 ^ m : ℕ) : ℝ) := by
  let k : ℝ := ((2 ^ m : ℕ) : ℝ)
  have hk : 0 < k := by positivity
  have h₁ : (⌊(a : ℝ) / k⌋ : ℝ) ≤ (a : ℝ) / k := Int.floor_le _
  have h₂ : (a : ℝ) / k < (⌊(a : ℝ) / k⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · have h₃ : (⌊(a : ℝ) / k⌋ : ℝ) * k ≤ ((a : ℝ) / k) * k := by gcongr
    have h₄ : ((a : ℝ) / k) * k = (a : ℝ) := by
      field_simp [hk.ne'] <;> ring
    rw [h₄] at h₃
    exact h₃
  · have h₃ : ((a : ℝ) / k) * k < ((⌊(a : ℝ) / k⌋ : ℝ) + 1) * k := by gcongr
    have h₄ : ((a : ℝ) / k) * k = (a : ℝ) := by
      field_simp [hk.ne'] <;> ring
    rw [h₄] at h₃
    exact h₃

/-- Two fine tubes with the same local slope cell have slopes within δ/Δ. -/
lemma same_slope_cell_slopes_close (n m : ℕ) (hnm : m ≤ n)
    (T U : DyadicTube n)
    (h : localSlopeCellIndex m T.a = localSlopeCellIndex m U.a) :
    |T.slope - U.slope| < dyadicDelta (n - m) := by
  let k : ℝ := ((2 ^ m : ℕ) : ℝ)
  have hk : 0 < k := by positivity
  have hδpos : 0 < dyadicDelta n := by
    apply Real.rpow_pos_of_pos <;> norm_num
  have h1 := localSlopeCellIndex_bounds m T.a
  have h2 := localSlopeCellIndex_bounds m U.a
  rw [h] at h1
  have h_diff : |(T.a : ℝ) - (U.a : ℝ)| < k := by
    rw [abs_lt] <;> constructor <;> linarith
  have hslope : T.slope - U.slope = ((T.a : ℝ) - (U.a : ℝ)) * dyadicDelta n := by
    simp [DyadicTube.slope] <;> ring
  rw [hslope]
  have h_abs : |((T.a : ℝ) - (U.a : ℝ)) * dyadicDelta n| =
      |(T.a : ℝ) - (U.a : ℝ)| * dyadicDelta n := by
    rw [abs_mul, abs_of_pos hδpos]
  rw [h_abs]
  have h3 : |(T.a : ℝ) - (U.a : ℝ)| * dyadicDelta n < k * dyadicDelta n := by
    gcongr <;> linarith
  have h_k_def : k = ((2 ^ m : ℕ) : ℝ) := by rfl
  have h4 : k * dyadicDelta n = dyadicDelta (n - m) := by
    rw [h_k_def]
    simp only [dyadicDelta]
    have h5 : (n : ℝ) = (m : ℝ) + ((n - m : ℕ) : ℝ) := by
      simp [Nat.cast_sub hnm] <;> ring
    rw [h5]
    simp [Real.rpow_add] <;> field_simp <;> ring
  linarith [h3, h4]

end SlopeCellLemmas

section GreedySeparation

/-- A subset `B'` is `c`-separated if distinct elements differ by more than `c`. -/
def IsCSeparated (c : ℕ) (B : Finset ℤ) : Prop :=
  ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → |b₁ - b₂| > (c : ℤ)

/-- If `b₁ % d = b₂ % d` for positive `d`, then `d ∣ b₁ - b₂`. -/
lemma same_mod_implies_dvd_sub (d : ℕ) (hd : 0 < d) (b1 b2 : ℤ)
    (h : b1 % (d : ℤ) = b2 % (d : ℤ)) : (d : ℤ) ∣ (b1 - b2) := by
  have h1 : (b1 - b2) % (d : ℤ) = 0 := by
    have h2 : (b1 - b2) % (d : ℤ) = ((b1 % (d : ℤ)) - (b2 % (d : ℤ))) % (d : ℤ) := by
      rw [Int.sub_emod]
    rw [h2, h]
    <;> simp
  omega

/-- Every finite set of integers contains a `c`-separated subset of size
at least `|B| / (c + 1)`. Uses residue classes modulo `c+1`. -/
lemma exists_c_separated_subset (c : ℕ) (B : Finset ℤ) :
    ∃ (B' : Finset ℤ), B' ⊆ B ∧ IsCSeparated c B' ∧
      (B.card : ℝ) ≤ ((c : ℝ) + 1) * (B'.card : ℝ) := by
  classical
  let d : ℕ := c + 1
  have hd_pos : 0 < d := by positivity
  have hdn : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  let part : ℤ → Fin d := fun b =>
    ⟨(b % (d : ℤ)).toNat, by
      have h₁ : 0 ≤ b % (d : ℤ) := Int.emod_nonneg b hdn
      have h₂ : b % (d : ℤ) < (d : ℤ) := Int.emod_lt b hdn
      have h₄ : (b % (d : ℤ)).toNat < d := by
        have h₅ : 0 ≤ b % (d : ℤ) := h₁
        have h₆ : ((b % (d : ℤ)).toNat : ℤ) = b % (d : ℤ) := by
          rw [Int.toNat_of_nonneg h₅]
        omega
      exact h₄⟩
  let Bpart : Fin d → Finset ℤ := fun r => B.filter (fun b => part b = r)
  have h_cover : ∀ b ∈ B, b ∈ Bpart (part b) := by
    intro b hb
    simp only [Bpart, Finset.mem_filter]
    <;> exact ⟨hb, by simp⟩
  have h_union : B = Finset.biUnion (Finset.univ : Finset (Fin d)) Bpart := by
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hb
      exact ⟨part b, h_cover b hb⟩
    · rintro ⟨r, hr⟩
      exact (Finset.mem_filter.mp hr).1
  have h_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin d)) Bpart := by
    intro r1 _ r2 _ hne
    simp only [Bpart, Finset.disjoint_left]
    intro b hb1 hb2
    have h1 : part b = r1 := (Finset.mem_filter.mp hb1).2
    have h2 : part b = r2 := (Finset.mem_filter.mp hb2).2
    rw [h1] at h2
    exact hne h2
  have h_card : (B.card : ℝ) = ∑ r : Fin d, ((Bpart r).card : ℝ) := by
    have h : B.card = ∑ r : Fin d, (Bpart r).card := by
      rw [h_union]
      rw [Finset.card_biUnion h_disj] <;> simp
    exact_mod_cast h
  -- Find r with Bpart r.card ≥ B.card / d
  have h_exists : ∃ (r : Fin d), (B.card : ℝ) ≤ (d : ℝ) * (Bpart r).card := by
    by_contra h
    push Not at h
    have h_lt : ∀ (i : Fin d), ((Bpart i).card : ℝ) < (B.card : ℝ) / (d : ℝ) := by
      intro i
      have h_i : (d : ℝ) * ((Bpart i).card : ℝ) < (B.card : ℝ) := h i
      have h_pos : (0 : ℝ) < (d : ℝ) := by positivity
      calc
        ((Bpart i).card : ℝ)
          = ((d : ℝ) * ((Bpart i).card : ℝ)) / (d : ℝ) := by field_simp [h_pos.ne'] <;> ring
        _ < (B.card : ℝ) / (d : ℝ) := by gcongr
    have h_nonempty : (Finset.univ : Finset (Fin d)).Nonempty := by
      exact ⟨⟨0, by omega⟩, by simp⟩
    have h_sum : (∑ r : Fin d, ((Bpart r).card : ℝ)) < ∑ r : Fin d, ((B.card : ℝ) / (d : ℝ)) := by
      exact Finset.sum_lt_sum_of_nonempty h_nonempty (fun i _ => h_lt i)
    have h_rhs : ∑ r : Fin d, ((B.card : ℝ) / (d : ℝ)) = (B.card : ℝ) := by
      simp [Finset.sum_const, hd_pos.ne'] <;> field_simp <;> ring
    rw [h_rhs] at h_sum
    rw [h_card] at h_sum
    exact lt_irrefl _ h_sum
  rcases h_exists with ⟨r, hr⟩
  refine' ⟨Bpart r, Finset.filter_subset _ _, _ , _⟩
  · -- IsCSeparated
    intro b1 hb1 b2 hb2 hne
    have h1 : part b1 = r := (Finset.mem_filter.mp hb1).2
    have h2 : part b2 = r := (Finset.mem_filter.mp hb2).2
    have h_eq : part b1 = part b2 := by rw [h1, h2]
    have hmod1 : (b1 % (d : ℤ)).toNat = (b2 % (d : ℤ)).toNat := by
      injection h_eq
    have h_nonneg1 : 0 ≤ b1 % (d : ℤ) := Int.emod_nonneg b1 hdn
    have h_nonneg2 : 0 ≤ b2 % (d : ℤ) := Int.emod_nonneg b2 hdn
    have hmod_eq : b1 % (d : ℤ) = b2 % (d : ℤ) := by
      have h5 : ((b1 % (d : ℤ)).toNat : ℤ) = b1 % (d : ℤ) := by
        rw [Int.toNat_of_nonneg h_nonneg1]
      have h6 : ((b2 % (d : ℤ)).toNat : ℤ) = b2 % (d : ℤ) := by
        rw [Int.toNat_of_nonneg h_nonneg2]
      omega
    have hdiv : (d : ℤ) ∣ (b1 - b2) := same_mod_implies_dvd_sub d hd_pos b1 b2 hmod_eq
    have hne' : b1 - b2 ≠ 0 := by omega
    have h_abs_dvd : (d : ℤ) ∣ |b1 - b2| := by
      exact (dvd_abs (d : ℤ) (b1 - b2)).mpr hdiv
    have h_abs : |b1 - b2| ≥ (d : ℤ) := Int.le_of_dvd (by positivity) h_abs_dvd
    have h : |b1 - b2| > (c : ℤ) := by
      have hd : (d : ℤ) = (c : ℤ) + 1 := by simp [d] <;> omega
      rw [hd] at h_abs <;> omega
    exact h
  · -- cardinality
    simpa [d] using hr

end GreedySeparation

end InductionOnScales
