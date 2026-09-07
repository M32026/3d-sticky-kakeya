module

/-
# OSW Ruzsa Corollaries 2.3 and 2.4
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.RuzsaTriangle
public import MyLeanRepo.OSWPrelude

@[expose] public section


open Classical Set ENNReal BigOperators

namespace ProductLikeIncidence.OSW

noncomputable section

abbrev Nreal (δ : ℝ) (A : Set ℝ) : ENNReal :=
  ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A))

/-- **Corollary 2.3**: `N(X+X,δ) · N(Y,δ) ≤ 9 · N(X+Y,δ)^2`. -/
lemma corollary2_3 {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hY_nonempty : Y.Nonempty) :
    Nreal δ (Set.image2 (· + ·) X X) * Nreal δ Y ≤
      9 * Nreal δ (Set.image2 (· + ·) X Y) *
        Nreal δ (Set.image2 (· + ·) X Y) := by
  have h := discretized_pluennecke_ruzsa_sum hδ hX hY hY_nonempty
  simpa [Nreal] using h

/-- **Corollary 2.4**: `N(X-Y,δ) · N(X,δ) · N(Y,δ) ≤ 81 · N(X+Y,δ)^3`. -/
lemma corollary2_4 {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hX_nonempty : X.Nonempty) (hY_nonempty : Y.Nonempty) :
    Nreal δ (Set.image2 (· - ·) X Y) * Nreal δ X * Nreal δ Y ≤
      81 * Nreal δ (Set.image2 (· + ·) X Y) *
        Nreal δ (Set.image2 (· + ·) X Y) *
        Nreal δ (Set.image2 (· + ·) X Y) := by
  set NXY := Nreal δ (Set.image2 (· + ·) X Y) with hNXY
  set NYY := Nreal δ (Set.image2 (· + ·) Y Y) with hNYY
  set NXmY := Nreal δ (Set.image2 (· - ·) X Y) with hNXmY
  set NX := Nreal δ X with hNX
  set NY := Nreal δ Y with hNY

  have h1 : NXmY * NY ≤ 9 * NXY * NYY := by
    have h := discretized_ruzsa_triangle hδ hX hY hY hY_nonempty
    simpa [Nreal, hNXmY, hNY, hNXY, hNYY] using h

  have h_comm : Set.image2 (· + ·) Y X = Set.image2 (· + ·) X Y := by
    ext z
    simp only [Set.mem_image2]
    constructor
    · rintro ⟨y, hy, x, hx, rfl⟩
      exact ⟨x, hx, y, hy, by ring⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨y, hy, x, hx, by ring⟩

  have h2 : NYY * NX ≤ 9 * NXY * NXY := by
    have h := discretized_pluennecke_ruzsa_sum hδ hY hX hX_nonempty
    simpa [Nreal, hNYY, hNX, hNXY, h_comm] using h

  have h3 : NXmY * NY * NX ≤ 9 * NXY * (NYY * NX) := by
    calc NXmY * NY * NX
      = (NXmY * NY) * NX := by rw [mul_assoc]
    _ ≤ (9 * NXY * NYY) * NX := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 9 * NXY * (NYY * NX) := by rw [mul_assoc, mul_assoc]

  have h4 : 9 * NXY * (NYY * NX) ≤ 9 * NXY * (9 * NXY * NXY) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)

  have h5 : 9 * NXY * (9 * NXY * NXY) = 81 * NXY * NXY * NXY := by
    have h_eq : (9 : ENNReal) * NXY * ((9 : ENNReal) * NXY * NXY) =
             (9 : ENNReal) * (9 : ENNReal) * (NXY * NXY * NXY) := by
      simp [mul_assoc, mul_left_comm] <;> rfl
    rw [h_eq]
    have h9 : (9 : ENNReal) * (9 : ENNReal) = (81 : ENNReal) := by norm_num
    rw [h9] <;> simp [mul_assoc] <;> rfl

  have h6 : NXmY * NX * NY = NXmY * NY * NX := by
    rw [mul_assoc, mul_assoc]
    <;> rw [mul_comm NX NY]
    <;> rw [←mul_assoc, ←mul_assoc]

  rw [h6]
  exact h3.trans (h4.trans h5.le)

/-- **Symmetric Corollary 2.4** with division:
    `N(X-X) ≤ 81 · N(X+X)^3 / N(X)^2`. -/
lemma corollary2_4_same {δ : ℝ} (hδ : 0 < δ) {X : Set ℝ}
    (hX : Bornology.IsBounded X) (hX_nonempty : X.Nonempty)
    (hN_finite : Nreal δ X ≠ 0) (hN_top : Nreal δ X ≠ ⊤) :
    Nreal δ (Set.image2 (· - ·) X X) ≤
      81 * Nreal δ (Set.image2 (· + ·) X X) *
        Nreal δ (Set.image2 (· + ·) X X) *
        Nreal δ (Set.image2 (· + ·) X X) /
        (Nreal δ X * Nreal δ X) := by
  let NX := Nreal δ X
  let NXX := Nreal δ (Set.image2 (· + ·) X X)
  let NmX := Nreal δ (Set.image2 (· - ·) X X)

  have h_main : NmX * NX * NX ≤ 81 * NXX * NXX * NXX :=
    corollary2_4 hδ hX hX hX_nonempty hX_nonempty

  have h_ne : NX * NX ≠ 0 := mul_ne_zero hN_finite hN_finite
  have h_top : NX * NX ≠ ⊤ := ENNReal.mul_ne_top hN_top hN_top

  have h_iff : NmX ≤ (81 * NXX * NXX * NXX) / (NX * NX) ↔
      NmX * (NX * NX) ≤ 81 * NXX * NXX * NXX :=
    ENNReal.le_div_iff_mul_le (Or.inl h_ne) (Or.inl h_top)

  have h_assoc : NmX * (NX * NX) = NmX * NX * NX := by
    rw [mul_assoc]

  rw [h_iff, h_assoc]
  exact h_main

end

end ProductLikeIncidence.OSW
