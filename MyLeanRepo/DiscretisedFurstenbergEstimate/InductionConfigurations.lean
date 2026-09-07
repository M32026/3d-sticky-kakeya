module

/-
  Shared geometric definitions for induction on scales.

  Extracted from archived InductionOnScales.lean to avoid compiler crash.
  Contains:
  - squareContained, containingSquare, squareHomothety
  - coarseAncestor, tubeAncestor
  - NiceConfiguration.tubeFamilyOpt extension

  Whiteprint node: induction_on_scales
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.InductionConfigurations

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Number of fine squares along one side of a coarse square. -/
def refinementFactor (n m : ℕ) : ℕ := 2 ^ (n - m)

/-- A fine square `p` is contained in coarse square `Q`. -/
def squareContained {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m) : Prop :=
  (Q.i : ℤ) * (refinementFactor n m) ≤ p.i ∧
  p.i < (Q.i + 1) * (refinementFactor n m) ∧
  (Q.j : ℤ) * (refinementFactor n m) ≤ p.j ∧
  p.j < (Q.j + 1) * (refinementFactor n m)

/-- A fine tube `T` has coarse ancestor `T'`. -/
def tubeAncestor {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) (T' : DyadicTube m) : Prop :=
  (T'.a : ℤ) * (refinementFactor n m) ≤ T.a ∧
  T.a < (T'.a + 1) * (refinementFactor n m) ∧
  (T'.b : ℤ) * (refinementFactor n m) ≤ T.b ∧
  T.b < (T'.b + 1) * (refinementFactor n m)

/-- The coarse square containing a fine square. -/
def containingSquare {n m : ℕ} (hnm : m ≤ n) (p : DyadicSquare n) :
    DyadicSquare m :=
  ⟨p.i / (refinementFactor n m), p.j / (refinementFactor n m)⟩

/-- The coarse ancestor of a fine tube (floor division). -/
def coarseAncestor {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    DyadicTube m :=
  ⟨T.a / (refinementFactor n m), T.b / (refinementFactor n m)⟩

/-- Homothety mapping fine square within Q to scale n-m. -/
def squareHomothety {n m : ℕ} (hnm : m ≤ n) (Q : DyadicSquare m)
    (p : DyadicSquare n) : DyadicSquare (n - m) :=
  ⟨p.i - Q.i * (refinementFactor n m),
   p.j - Q.j * (refinementFactor n m)⟩

/-- Total tube family without membership proof requirement. -/
noncomputable def tubeFamilyOpt {n s C M}
    (config : NiceConfiguration n s C M)
    (p : DyadicSquare n) : Finset (DyadicTube n) :=
  if hp : p ∈ config.P₀ then config.tubeFamily p hp else ∅

lemma tubeFamilyOpt_eq {n s C M}
    (config : NiceConfiguration n s C M)
    {p : DyadicSquare n} (hp : p ∈ config.P₀) :
    tubeFamilyOpt config p = config.tubeFamily p hp := by
  rw [tubeFamilyOpt, dif_pos hp]

lemma int_ediv_iff (x q : ℤ) {k : ℕ} (hk_pos : 0 < k) :
    x / (k : ℤ) = q ↔ q * (k : ℤ) ≤ x ∧ x < (q + 1) * (k : ℤ) := by
  let k' : ℤ := ↑k
  have hk'_pos : 0 < k' := by
    exact Nat.cast_pos.mpr hk_pos
  have hk'_ne : k' ≠ 0 := ne_of_gt hk'_pos
  constructor
  · intro h
    have h_div : x / k' = q := h
    have h1 : x = (x / k') * k' + x % k' :=
      Eq.symm (Int.ediv_mul_add_emod x k')
    rw [h_div] at h1
    have h2 : 0 ≤ x % k' := Int.emod_nonneg x hk'_ne
    have h3 : x % k' < k' := Int.emod_lt_of_pos x hk'_pos
    rw [h1]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    set r := x / k' with hr
    have h3 : r * k' ≤ x := Int.ediv_mul_le x hk'_ne
    have h4 : x % k' < k' := Int.emod_lt_of_pos x hk'_pos
    have h5 : x = r * k' + x % k' := by
      simp [Int.emod_def, hr] <;> ring
    have h6 : x < (r + 1) * k' := by rw [h5] <;> linarith
    have h7 : r ≤ q := by nlinarith
    have h8 : q ≤ r := by nlinarith
    omega

/-- `containingSquare p = Q` iff `squareContained p Q`. -/
lemma containingSquare_iff {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m) :
    containingSquare hnm p = Q ↔ squareContained hnm p Q := by
  let k := refinementFactor n m
  have hk_pos : 0 < k := by
    dsimp only [k, refinementFactor]
    exact pow_pos (by norm_num) (n - m)
  constructor
  · intro h
    have hi : (containingSquare hnm p).i = Q.i := by rw [h]
    have hj : (containingSquare hnm p).j = Q.j := by rw [h]
    simp only [containingSquare] at hi hj
    have h1 := (int_ediv_iff p.i Q.i hk_pos).mp hi
    have h2 := (int_ediv_iff p.j Q.j hk_pos).mp hj
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hi : p.i / (k : ℤ) = Q.i := (int_ediv_iff p.i Q.i hk_pos).mpr ⟨h1, h2⟩
    have hj : p.j / (k : ℤ) = Q.j := (int_ediv_iff p.j Q.j hk_pos).mpr ⟨h3, h4⟩
    have h : containingSquare hnm p = Q := by
      cases p
      cases Q
      simp [containingSquare, hi, hj]
      <;> aesop
    exact h

end DiscretisedFurstenbergEstimate.InductionConfigurations
