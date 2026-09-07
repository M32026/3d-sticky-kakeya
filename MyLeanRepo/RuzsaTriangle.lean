module

/-
# Discretized Ruzsa triangle inequality

Proves `discretized_ruzsa_triangle`:
`N(X-Y, δ) · N(Z, δ) ≤ 9 · N(X+Z, δ) · N(Z+Y, δ)`

for bounded subsets of ℝ, using dyadic covering numbers.

Reuses cube-index-set infrastructure from `DiscretizedPluennecke`.

## Proof route

1. Use `realCubeIndexSet` and `realCoveringNumber_eq_card` from `DiscretizedPluennecke`.
2. General difference-index inclusion: I(X-Y) ⊆ I(X) - I(Y) + {-1, 0}.
3. Sum-index inclusion: I(X) + I(Z) ⊆ I(X+Z) + {-1, 0} (already in DiscretizedPluennecke).
4. Apply finite-set Ruzsa triangle: |I(X)-I(Y)|·|I(Z)| ≤ |I(X)+I(Z)|·|I(Z)+I(Y)|.
5. Combine factor-2 losses: N(X-Y)·N(Z) ≤ 8·N(X+Z)·N(Z+Y) ≤ 9·...
-/

public import MyLeanRepo.DiscretizedPluenneckeFull
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence


/-- Discretized Ruzsa triangle inequality for 1D dyadic covering numbers.

`N(X-Y, δ) · N(Z, δ) ≤ 9 · N(X+Z, δ) · N(Z+Y, δ)` -/
lemma discretized_ruzsa_triangle {δ : ℝ} (hδ : 0 < δ) {X Y Z : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hZ : Bornology.IsBounded Z) (hZ_nonempty : Z.Nonempty) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· - ·) X Y))) *
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Z)) ≤
    9 * ENat.toENNReal (dyadicCoveringNumber δ
      (productLikeRealLineCopy (Set.image2 (· + ·) X Z))) *
      ENat.toENNReal (dyadicCoveringNumber δ
        (productLikeRealLineCopy (Set.image2 (· + ·) Z Y))) := by
  let hXY_bdd := bounded_image2_sub hX hY
  let hXZ_bdd := bounded_image2_add hX hZ
  let hZY_bdd := bounded_image2_add hZ hY
  let IX := (realCubeIndexSet_finite hδ hX).toFinset
  let IY := (realCubeIndexSet_finite hδ hY).toFinset
  let IZ := (realCubeIndexSet_finite hδ hZ).toFinset
  let IXY := (realCubeIndexSet_finite hδ hXY_bdd).toFinset
  let IXZ := (realCubeIndexSet_finite hδ hXZ_bdd).toFinset
  let IZY := (realCubeIndexSet_finite hδ hZY_bdd).toFinset
  have hIX : (IX : Set ℤ) = realCubeIndexSet δ X := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hX)
  have hIY : (IY : Set ℤ) = realCubeIndexSet δ Y := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hY)
  have hIZ : (IZ : Set ℤ) = realCubeIndexSet δ Z := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hZ)
  have hIXY : (IXY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· - ·) X Y) := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hXY_bdd)
  have hIXZ : (IXZ : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Z) := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hXZ_bdd)
  have hIZY : (IZY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) Z Y) := by exact Set.Finite.coe_toFinset (realCubeIndexSet_finite hδ hZY_bdd)
  let E : Finset ℤ := {-1, 0}
  have hE2 : E.card = 2 := by decide
  have h1 : IXY ⊆ (IX - IY) + E := by
    intro x hx
    have hx' : x ∈ realCubeIndexSet δ (Set.image2 (· - ·) X Y) := by
      have h : x ∈ (IXY : Set ℤ) := by exact_mod_cast hx
      rw [hIXY] at h; exact h
    have h_incl := diff_index_inclusion hδ hx'
    rcases h_incl with ⟨d, hd, e, he, rfl⟩
    rcases hd with ⟨i, hi, j, hj, rfl⟩
    have hi' : i ∈ IX := by
      have h : i ∈ (IX : Set ℤ) := by rw [hIX] <;> exact hi
      exact_mod_cast h
    have hj' : j ∈ IY := by
      have h : j ∈ (IY : Set ℤ) := by rw [hIY] <;> exact hj
      exact_mod_cast h
    have hde : i - j ∈ (IX - IY) := by exact Finset.sub_mem_sub hi' hj'
    have hee : e ∈ E := by simpa [E] using he
    have h_final : (i - j) + e ∈ (IX - IY) + E := Finset.add_mem_add hde hee
    exact h_final
  have h2 : (IX + IZ) ⊆ IXZ + E := by
    intro x hx
    have hx' : x ∈ realCubeIndexSet δ X + realCubeIndexSet δ Z := by
      rcases Finset.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
      have ha' : a ∈ realCubeIndexSet δ X := by
        have h : a ∈ (IX : Set ℤ) := by exact_mod_cast ha
        rw [hIX] at h
        exact h
      have hb' : b ∈ realCubeIndexSet δ Z := by
        have h : b ∈ (IZ : Set ℤ) := by exact_mod_cast hb
        rw [hIZ] at h
        exact h
      exact Set.mem_add.mpr ⟨a, ha', b, hb', rfl⟩
    have h_incl := sum_index_inclusion hδ hx'
    rcases h_incl with ⟨d, hd, e, he, rfl⟩
    have hd' : d ∈ IXZ := by
      have h : d ∈ (IXZ : Set ℤ) := by rw [hIXZ] <;> exact hd
      exact_mod_cast h
    have he' : e ∈ E := by simpa [E] using he
    have h_final : d + e ∈ IXZ + E := Finset.add_mem_add hd' he'
    exact h_final
  have h3 : (IZ + IY) ⊆ IZY + E := by
    intro x hx
    have hx' : x ∈ realCubeIndexSet δ Z + realCubeIndexSet δ Y := by
      rcases Finset.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
      have ha' : a ∈ realCubeIndexSet δ Z := by
        have h : a ∈ (IZ : Set ℤ) := by exact_mod_cast ha
        rw [hIZ] at h
        exact h
      have hb' : b ∈ realCubeIndexSet δ Y := by
        have h : b ∈ (IY : Set ℤ) := by exact_mod_cast hb
        rw [hIY] at h
        exact h
      exact Set.mem_add.mpr ⟨a, ha', b, hb', rfl⟩
    have h_incl := sum_index_inclusion hδ hx'
    rcases h_incl with ⟨d, hd, e, he, rfl⟩
    have hd' : d ∈ IZY := by
      have h : d ∈ (IZY : Set ℤ) := by rw [hIZY] <;> exact hd
      exact_mod_cast h
    have he' : e ∈ E := by simpa [E] using he
    have h_final : d + e ∈ IZY + E := Finset.add_mem_add hd' he'
    exact h_final
  have h_card1 : IXY.card ≤ 2 * (IX - IY).card := by
    have h4 : IXY ⊆ (IX - IY) + E := h1
    have h5 : ((IX - IY) + E).card ≤ 2 * (IX - IY).card := by
      calc ((IX - IY) + E).card
          ≤ ((IX - IY) ×ˢ E).card := Finset.card_image_le
        _ = (IX - IY).card * E.card := by rw [Finset.card_product]
        _ = (IX - IY).card * 2 := by rw [hE2] <;> ring
        _ = 2 * (IX - IY).card := by ring
    exact le_trans (Finset.card_le_card h4) h5
  have h_card2 : (IX + IZ).card ≤ 2 * IXZ.card := by
    have h4 : (IX + IZ) ⊆ IXZ + E := h2
    have h5 : (IXZ + E).card ≤ 2 * IXZ.card := by
      calc (IXZ + E).card
          ≤ (IXZ ×ˢ E).card := Finset.card_image_le
        _ = IXZ.card * E.card := by rw [Finset.card_product]
        _ = IXZ.card * 2 := by rw [hE2] <;> ring
        _ = 2 * IXZ.card := by ring
    exact le_trans (Finset.card_le_card h4) h5
  have h_card3 : (IZ + IY).card ≤ 2 * IZY.card := by
    have h4 : (IZ + IY) ⊆ IZY + E := h3
    have h5 : (IZY + E).card ≤ 2 * IZY.card := by
      calc (IZY + E).card
          ≤ (IZY ×ˢ E).card := Finset.card_image_le
        _ = IZY.card * E.card := by rw [Finset.card_product]
        _ = IZY.card * 2 := by rw [hE2] <;> ring
        _ = 2 * IZY.card := by ring
    exact le_trans (Finset.card_le_card h4) h5
  have h_ruzsa : (IX - IY).card * IZ.card ≤ (IX + IZ).card * (IZ + IY).card := by
    have h := Finset.ruzsa_triangle_inequality_sub_add_add IX IZ IY
    have h_comm : (IY + IZ).card = (IZ + IY).card := by
      have h_eq : (IY + IZ) = (IZ + IY) := by
        ext z; simp [Finset.mem_add, add_comm] <;> tauto
      rw [h_eq]
    rw [h_comm] at h
    exact h
  have h_main : IXY.card * IZ.card ≤ 8 * IXZ.card * IZY.card := by
    calc
      IXY.card * IZ.card
        ≤ (2 * (IX - IY).card) * IZ.card := by gcongr
      _ = 2 * ((IX - IY).card * IZ.card) := by ring
      _ ≤ 2 * ((IX + IZ).card * (IZ + IY).card) := by gcongr
      _ ≤ 2 * ((2 * IXZ.card) * (2 * IZY.card)) := by gcongr
      _ = 8 * IXZ.card * IZY.card := by ring
  have h_main' : (ENat.toENNReal ↑IXY.card) * (ENat.toENNReal ↑IZ.card) ≤
      8 * (ENat.toENNReal ↑IXZ.card) * (ENat.toENNReal ↑IZY.card) := by
    exact_mod_cast h_main
  have hNXY' := realCoveringNumber_eq_card hδ hXY_bdd
  have hNZ' := realCoveringNumber_eq_card hδ hZ
  have hNXZ' := realCoveringNumber_eq_card hδ hXZ_bdd
  have hNZY' := realCoveringNumber_eq_card hδ hZY_bdd
  have h1c : ENat.toENNReal (realCubeIndexSet δ (Set.image2 (· - ·) X Y)).encard = ENat.toENNReal ↑IXY.card := by
    have h1a : (realCubeIndexSet δ (Set.image2 (· - ·) X Y)).encard = ↑IXY.card := by rw [←hIXY] <;> simp
    rw [h1a] <;> rfl
  have h2c : ENat.toENNReal (realCubeIndexSet δ Z).encard = ENat.toENNReal ↑IZ.card := by
    have h2a : (realCubeIndexSet δ Z).encard = ↑IZ.card := by rw [←hIZ] <;> simp
    rw [h2a] <;> rfl
  have h3c : ENat.toENNReal (realCubeIndexSet δ (Set.image2 (· + ·) X Z)).encard = ENat.toENNReal ↑IXZ.card := by
    have h3a : (realCubeIndexSet δ (Set.image2 (· + ·) X Z)).encard = ↑IXZ.card := by rw [←hIXZ] <;> simp
    rw [h3a] <;> rfl
  have h4c : ENat.toENNReal (realCubeIndexSet δ (Set.image2 (· + ·) Z Y)).encard = ENat.toENNReal ↑IZY.card := by
    have h4a : (realCubeIndexSet δ (Set.image2 (· + ·) Z Y)).encard = ↑IZY.card := by rw [←hIZY] <;> simp
    rw [h4a] <;> rfl
  have h_final8 : ENat.toENNReal (dyadicCoveringNumber δ
        (productLikeRealLineCopy (Set.image2 (· - ·) X Y))) *
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Z)) ≤
      8 * ENat.toENNReal (dyadicCoveringNumber δ
          (productLikeRealLineCopy (Set.image2 (· + ·) X Z))) *
        ENat.toENNReal (dyadicCoveringNumber δ
          (productLikeRealLineCopy (Set.image2 (· + ·) Z Y))) := by
    have h_a : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· - ·) X Y))) =
        ENat.toENNReal ↑IXY.card := by
      rw [realCoveringNumber_eq_card hδ hXY_bdd, h1c]
    have h_b : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy Z)) =
        ENat.toENNReal ↑IZ.card := by
      rw [realCoveringNumber_eq_card hδ hZ, h2c]
    have h_c : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) X Z))) =
        ENat.toENNReal ↑IXZ.card := by
      rw [realCoveringNumber_eq_card hδ hXZ_bdd, h3c]
    have h_d : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) Z Y))) =
        ENat.toENNReal ↑IZY.card := by
      rw [realCoveringNumber_eq_card hδ hZY_bdd, h4c]
    rw [h_a, h_b, h_c, h_d]
    exact h_main'
  have h_le89 : (8 : ENNReal) ≤ 9 := by norm_num
  have h_goal : 8 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) X Z))) *
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) Z Y))) ≤
      9 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) X Z))) *
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (Set.image2 (· + ·) Z Y))) := by
    gcongr
    <;> norm_num
  exact le_trans h_final8 h_goal

end ProductLikeIncidence
