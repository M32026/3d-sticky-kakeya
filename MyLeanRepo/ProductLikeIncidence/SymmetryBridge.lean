module

/-
# Symmetry Bridge: B1-B2 difference bound from B2-B1

Closes the explicit "symmetry gap" in `glue_h5_to_h6`: the hypothesis
`h_diff_B1B2_over_B2_raw` follows from `h_diff_B2B1_over_B2_raw` by negation
symmetry of difference sets.

## Key fact

For finite δ-grid-aligned sets `B1`, `B2`:
- `Set.image2 (· - ·) B1 B2 = Set.image (fun x => -x) (Set.image2 (· - ·) B2 B1)`
- Both difference sets are finite, δ-grid-aligned, and δ-separated.
- For such sets, `Nreal δ S = ENNReal.ofReal (S.ncard : ℝ)`.
- Negation is injective, so the two difference sets have the same ncard.
- Therefore `Nreal δ (image2 (-) B1 B2) = Nreal δ (image2 (-) B2 B1)`.

Thus any upper bound on one is also an upper bound on the other.

## Whiteprint node

Bridge for the symmetry gap in `glue_h5_to_h6`.
-/

public import MyLeanRepo.ProductLikeIncidence.GridSeparatedCard
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set

namespace ProductLikeIncidence.ProductReduction

/-- **Difference set negation identity**:
`B1 - B2 = -(B2 - B1)`. -/
lemma diff_set_neg_identity
    {B1 B2 : Set ℝ} :
    Set.image2 (· - ·) B1 B2 =
      Set.image (fun x : ℝ => -x) (Set.image2 (· - ·) B2 B1) := by
  ext z
  simp only [Set.mem_image, Set.mem_image2]
  constructor
  · rintro ⟨b1, hb1, b2, hb2, rfl⟩
    refine ⟨b2 - b1, ⟨b2, hb2, b1, hb1, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨b2, hb2, b1, hb1, rfl⟩, rfl⟩
    exact ⟨b1, hb1, b2, hb2, by ring⟩

/-- **Difference set of grid-aligned sets is grid-aligned**. -/
lemma diff_set_grid
    {δ : ℝ} {B1 B2 : Set ℝ}
    (hB1_grid : ∀ x ∈ B1, x ∈ productLikeIntegerGrid δ)
    (hB2_grid : ∀ x ∈ B2, x ∈ productLikeIntegerGrid δ) :
    ∀ z ∈ Set.image2 (· - ·) B1 B2, z ∈ productLikeIntegerGrid δ := by
  intro z hz
  rcases hz with ⟨b1, hb1, b2, hb2, hz_eq⟩
  rcases hB1_grid b1 hb1 with ⟨k, hk⟩
  rcases hB2_grid b2 hb2 with ⟨j, hj⟩
  have h_z_eq : z = b1 - b2 := hz_eq.symm
  rw [h_z_eq, hk, hj]
  refine ⟨k - j, ?_⟩
  simp [mul_sub]

/-- **Difference set of δ-separated grid sets is δ-separated**.

Since all points lie on the δ-grid, any two distinct differences differ by
an integer multiple of δ, hence by at least δ. -/
lemma diff_set_separated
    {δ : ℝ} {B1 B2 : Set ℝ}
    (hδ_pos : 0 < δ)
    (hB1_grid : ∀ x ∈ B1, x ∈ productLikeIntegerGrid δ)
    (hB2_grid : ∀ x ∈ B2, x ∈ productLikeIntegerGrid δ) :
    ∀ z ∈ Set.image2 (· - ·) B1 B2,
      ∀ w ∈ Set.image2 (· - ·) B1 B2, z ≠ w → |z - w| ≥ δ := by
  intro z hz w hw hne
  rcases hz with ⟨b1, hb1, b2, hb2, rfl⟩
  rcases hw with ⟨b1', hb1', b2', hb2', rfl⟩
  rcases hB1_grid b1 hb1 with ⟨k, hk⟩
  rcases hB2_grid b2 hb2 with ⟨j, hj⟩
  rcases hB1_grid b1' hb1' with ⟨k', hk'⟩
  rcases hB2_grid b2' hb2' with ⟨j', hj'⟩
  set n : ℤ := (k - k') - (j - j') with hn_def
  have h_n_eq : ((n : ℝ)) = ((k : ℝ) - (k' : ℝ)) - ((j : ℝ) - (j' : ℝ)) := by
    simp [hn_def] <;> norm_cast <;> ring
  have h_diff : (b1 - b2) - (b1' - b2') = δ * (n : ℝ) := by
    rw [hk, hj, hk', hj', h_n_eq] <;> ring
  have h_ne : n ≠ 0 := by
    intro h
    have h9 : (b1 - b2) - (b1' - b2') = 0 := by
      rw [h_diff]
      simp [h]
    have h10 : b1 - b2 = b1' - b2' := by linarith
    exact hne h10
  have h1 : 1 ≤ |(n : ℝ)| := by
    have h2 : 0 < |n| := abs_pos.mpr h_ne
    exact_mod_cast h2
  have h_abs : |(b1 - b2) - (b1' - b2')| = δ * |(n : ℝ)| := by
    rw [h_diff]
    have h3 : |δ * (n : ℝ)| = |δ| * |(n : ℝ)| := abs_mul δ (n : ℝ)
    rw [h3]
    have h4 : |δ| = δ := abs_of_pos hδ_pos
    rw [h4] <;> ring
  rw [h_abs]
  have h3 : δ * |(n : ℝ)| ≥ δ := by
    calc δ * |(n : ℝ)| ≥ δ * 1 := by gcongr
      _ = δ := by ring
  exact h3

/-- **Nreal invariance under negation for finite grid-separated sets**.

For a finite, δ-grid-aligned, δ-separated set `S`, negation preserves
the `Nreal` value exactly. -/
lemma nreal_neg_invariant
    {δ : ℝ} {S : Set ℝ}
    (hδ_pos : 0 < δ)
    (hS_finite : S.Finite)
    (hS_grid : ∀ x ∈ S, x ∈ productLikeIntegerGrid δ)
    (hS_separated : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → |x - y| ≥ δ) :
    Nreal δ (Set.image (fun x : ℝ => -x) S) = Nreal δ S := by
  let S_neg := Set.image (fun x : ℝ => -x) S
  have hS_neg_finite : S_neg.Finite := hS_finite.image _
  have hS_neg_grid : ∀ x ∈ S_neg, x ∈ productLikeIntegerGrid δ := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hS_grid y hy with ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    simp
  have hS_neg_separated : ∀ x ∈ S_neg, ∀ y ∈ S_neg, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hne
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have hne' : x' ≠ y' := by
      intro h
      rw [h] at hne
      exact hne rfl
    have h : |(-x') - (-y')| = |x' - y'| := by
      have h2 : (-x') - (-y') = -(x' - y') := by ring
      rw [h2, abs_neg]
    rw [h]
    exact hS_separated x' hx' y' hy' hne'
  have h_inj : Set.InjOn (fun x : ℝ => -x) S := by
    intro a _ b _ h
    simpa using h
  have h_ncard_eq : S_neg.ncard = S.ncard := by
    exact InjOn.ncard_image h_inj
  have h1 : Nreal δ S_neg = ENNReal.ofReal (S_neg.ncard : ℝ) :=
    grid_separated_nreal_eq_card1d hδ_pos hS_neg_finite hS_neg_grid hS_neg_separated
  have h2 : Nreal δ S = ENNReal.ofReal (S.ncard : ℝ) :=
    grid_separated_nreal_eq_card1d hδ_pos hS_finite hS_grid hS_separated
  rw [h1, h2, h_ncard_eq]

/-- **Symmetry bridge**: B1-B2 difference bound from B2-B1 bound.

Given `h_diff_B2B1_over_B2`:
`Nreal δ (image2 (-) B2 B1) ≤ 2 * ofReal(K * R) * Nreal δ B2`

Conclude `h_diff_B1B2_over_B2`:
`Nreal δ (image2 (-) B1 B2) ≤ 2 * ofReal(K * R) * Nreal δ B2`

This closes the explicit symmetry gap in `glue_h5_to_h6`. -/
lemma symmetry_bridge_B1B2_diff
    {δ : ℝ} {B1 B2 : Set ℝ} {K R : ℝ}
    (hδ_pos : 0 < δ)
    (hB1_finite : B1.Finite)
    (hB2_finite : B2.Finite)
    (hB1_grid : ∀ x ∈ B1, x ∈ productLikeIntegerGrid δ)
    (hB2_grid : ∀ x ∈ B2, x ∈ productLikeIntegerGrid δ)
    (h_diff_B2B1_over_B2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
        (2 : ENNReal) * ENNReal.ofReal (K * R) * Nreal δ B2) :
    Nreal δ (Set.image2 (· - ·) B1 B2) ≤
      (2 : ENNReal) * ENNReal.ofReal (K * R) * Nreal δ B2 := by
  let D21 := Set.image2 (· - ·) B2 B1
  let D12 := Set.image2 (· - ·) B1 B2
  have hD21_finite : D21.Finite := by exact Finite.image2 (fun x1 x2 => x1 - x2) hB2_finite hB1_finite
  have hD21_grid : ∀ z ∈ D21, z ∈ productLikeIntegerGrid δ :=
    diff_set_grid hB2_grid hB1_grid
  have hD21_sep : ∀ z ∈ D21, ∀ w ∈ D21, z ≠ w → |z - w| ≥ δ :=
    diff_set_separated hδ_pos hB2_grid hB1_grid
  have h_eq : D12 = Set.image (fun x : ℝ => -x) D21 :=
    diff_set_neg_identity
  have hNreal_eq : Nreal δ D12 = Nreal δ D21 := by
    rw [h_eq]
    exact nreal_neg_invariant hδ_pos hD21_finite hD21_grid hD21_sep
  rw [hNreal_eq]
  exact h_diff_B2B1_over_B2

end ProductLikeIncidence.ProductReduction

end
