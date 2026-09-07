module

/-
# Helper lemmas for Strong Ring Theorem Steps 9–12

Standard dyadic cube index counting arguments:
1. `covering_negation_le_two`: N(-S) ≤ 2N(S)
2. `ruzsa_triangle_sub_sub_sub`: N(X-Z)N(Y) ≤ 36 N(X-Y)N(Y-Z)
3. `covering_scale_down_le_two`: N(rS) ≤ 2N(S) for 0<r≤1
4. `covering_scale_down_ge`: N(S) ≤ C·N(rS) for c≤r≤1
5. `covering_NA_ge_NB`: N(A) ≥ (δ^c/3)·N(t⁻¹A) for δ^c≤t≤1
6. `covering_sumset_trivial`: N(X+Y) ≤ 4N(X)N(Y)
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.RuzsaTriangle
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators Pointwise

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

noncomputable section

open ProductLikeIncidence (realCubeIndexSet realCubeIndexSet_finite
  realCoveringNumber_eq_card bounded_image2_add bounded_image2_sub
  discretized_ruzsa_triangle)

/-- Negation of a real set. -/
def negSet (S : Set ℝ) : Set ℝ := (fun x : ℝ => -x) '' S

/-- Boundedness is preserved under negation. -/
lemma negSet_bounded {S : Set ℝ} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (negSet S) := by
  simpa [negSet] using hS.image (-(ContinuousLinearMap.id ℝ ℝ))

/-- Helper: integers in an open interval of length ≤ C have cardinality ≤ C. -/
lemma ints_in_open_interval_bound {a b : ℝ} {C : ℕ} (h : (b - a : ℝ) ≤ (C : ℝ))
    {s : Finset ℤ} (hs : ∀ x ∈ s, a < (x : ℝ) ∧ (x : ℝ) < b) : s.card ≤ C := by
  let lo := Int.floor a
  let hi := Int.ceil b
  have h1 : s ⊆ Finset.Ioo lo hi := by
    intro x hx
    have h2 := hs x hx
    simp only [Finset.mem_Ioo]
    constructor
    · have h3 : (lo : ℝ) ≤ a := Int.floor_le a
      have h4 : (lo : ℝ) < (x : ℝ) := by linarith
      exact_mod_cast h4
    · have h5 : (b : ℝ) ≤ (hi : ℝ) := Int.le_ceil b
      have h6 : (x : ℝ) < (hi : ℝ) := by linarith
      exact_mod_cast h6
  have h3 : s.card ≤ (Finset.Ioo lo hi).card := Finset.card_le_card h1
  have h4 : (Finset.Ioo lo hi).card ≤ C := by
    by_cases h5 : lo < hi
    · have h6 : ((Finset.Ioo lo hi).card : ℤ) = hi - lo - 1 := Int.card_Ioo_of_lt lo hi h5
      have h71 : (hi : ℝ) < b + 1 := Int.ceil_lt_add_one b
      have h72 : a < (lo : ℝ) + 1 := Int.lt_floor_add_one a
      have h7 : ((hi : ℝ) - (lo : ℝ) - 1 : ℝ) < (b - a : ℝ) + 1 := by linarith
      have h10 : ((hi - lo - 1 : ℤ) : ℝ) < (C : ℝ) + 1 := by
        have h101 : ((hi - lo - 1 : ℤ) : ℝ) = (hi : ℝ) - (lo : ℝ) - 1 := by simp
        rw [h101]
        linarith
      have h11 : (hi - lo - 1 : ℤ) < (C + 1 : ℤ) := by exact_mod_cast h10
      have h12 : hi - lo - 1 ≤ (C : ℤ) := by omega
      rw [← Nat.cast_le (α := ℤ)]
      rw [h6]
      exact h12
    · have h9 : Finset.Ioo lo hi = ∅ := by
        rw [Finset.Ioo_eq_empty]
        exact h5
      rw [h9] <;> simp
  exact h3.trans h4

/-! ### 1. Negation bound -/

/-- `N(-S) ≤ 2·N(S)`. Each cube of `-S` maps to at most 2 cubes of `S`. -/
lemma covering_negation_le_two {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) :
    Nreal δ (negSet S) ≤ 2 * Nreal δ S := by
  let IS := (realCubeIndexSet_finite hδ hS).toFinset
  let hnegS : Bornology.IsBounded (negSet S) := negSet_bounded hS
  let I_S := (realCubeIndexSet_finite hδ hnegS).toFinset
  have hIS : (IS : Set ℤ) = realCubeIndexSet δ S := Set.Finite.coe_toFinset _
  have hI_S : (I_S : Set ℤ) = realCubeIndexSet δ (negSet S) := Set.Finite.coe_toFinset _
  have h_main : I_S ⊆ IS.image (fun k : ℤ => -k) ∪ IS.image (fun k : ℤ => -k - 1) := by
    apply Finset.coe_subset.mp
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, hI_S, hIS]
    intro k hk
    simp only [realCubeIndexSet, Set.mem_setOf_eq, negSet, Set.mem_image] at hk
    rcases hk with ⟨y, ⟨hy1, hy2⟩, x, hxS, rfl⟩
    have hy1' : δ * (k : ℝ) ≤ -x := hy1
    have hy2' : -x < δ * ((k : ℝ) + 1) := hy2
    let j : ℤ := Int.floor (x / δ)
    have hj1 : δ * (j : ℝ) ≤ x := by
      have h : (j : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (j : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj2 : x < δ * ((j : ℝ) + 1) := by
      have h : x / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((j : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hjS : j ∈ realCubeIndexSet δ S := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x, ⟨hj1, hj2⟩, hxS⟩
    have h5 : (k : ℝ) ≤ -(j : ℝ) := by
      have h10 : -x ≤ -δ * (j : ℝ) := by linarith [hj1]
      have h11 : δ * (k : ℝ) ≤ -δ * (j : ℝ) := by linarith [hy1', h10]
      have h12 : δ * ((k : ℝ) + (j : ℝ)) ≤ 0 := by linarith
      have h13 : (k : ℝ) + (j : ℝ) ≤ 0 := by
        nlinarith [hδ]
      linarith
    have h6 : -(j : ℝ) - 2 < (k : ℝ) := by
      have h10 : -δ * ((j : ℝ) + 1) < -x := by linarith [hj2]
      have h11 : -δ * ((j : ℝ) + 1) < δ * ((k : ℝ) + 1) := by linarith [hy2', h10]
      have h12 : δ * (-((j : ℝ) + 1)) < δ * ((k : ℝ) + 1) := by
        have h121 : δ * (-((j : ℝ) + 1)) = -δ * ((j : ℝ) + 1) := by ring
        rw [h121]
        exact h11
      have h13 : -((j : ℝ) + 1) < (k : ℝ) + 1 := by nlinarith [hδ]
      linarith
    have h_k1 : k = -j ∨ k = -j - 1 := by
      have h7 : k ≤ -j := by exact_mod_cast h5
      have h8 : -j - 2 < k := by exact_mod_cast h6
      omega
    rcases h_k1 with (rfl | rfl)
    · exact Or.inl ⟨j, hjS, by simp⟩
    · exact Or.inr ⟨j, hjS, by simp⟩
  have h_inj1 : Function.Injective (fun k : ℤ => -k) := by
    intro a b h; simpa using h
  have h_inj2 : Function.Injective (fun k : ℤ => -k - 1) := by
    intro a b h; simpa using h
  have h_card : I_S.card ≤ 2 * IS.card := by
    calc I_S.card
      ≤ (IS.image (fun k : ℤ => -k) ∪ IS.image (fun k : ℤ => -k - 1)).card :=
        Finset.card_le_card h_main
    _ ≤ (IS.image (fun k : ℤ => -k)).card + (IS.image (fun k : ℤ => -k - 1)).card :=
        Finset.card_union_le _ _
    _ = IS.card + IS.card := by
      rw [Finset.card_image_of_injective IS h_inj1, Finset.card_image_of_injective IS h_inj2] <;> ring
    _ = 2 * IS.card := by ring
  have hN_S := realCoveringNumber_eq_card hδ hnegS
  have hNS := realCoveringNumber_eq_card hδ hS
  dsimp only [Nreal] at *
  rw [hN_S, hNS]
  have h_encard_S : (realCubeIndexSet δ (negSet S)).encard = I_S.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hnegS)] <;> rfl
  have h_encard_S2 : (realCubeIndexSet δ S).encard = IS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hS)] <;> rfl
  rw [h_encard_S, h_encard_S2]
  norm_cast <;> exact_mod_cast h_card

/-! ### 2. Ruzsa triangle sub-sub-sub -/

/-- `N(X-Z) · N(Y) ≤ 36 · N(X-Y) · N(Y-Z)`. -/
lemma ruzsa_triangle_sub_sub_sub {δ : ℝ} (hδ : 0 < δ) {X Y Z : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y)
    (hZ : Bornology.IsBounded Z) (hY_nonempty : Y.Nonempty) :
    Nreal δ (Set.image2 (· - ·) X Z) * Nreal δ Y ≤
      36 * Nreal δ (Set.image2 (· - ·) X Y) *
        Nreal δ (Set.image2 (· - ·) Y Z) := by
  have h_negY_bdd : Bornology.IsBounded (negSet Y) := negSet_bounded hY
  have h_negY_nonempty : (negSet Y).Nonempty := hY_nonempty.image _
  have h1 : Nreal δ (negSet Y) ≤ 2 * Nreal δ Y :=
    covering_negation_le_two hδ hY
  have h2 : Nreal δ Y ≤ 2 * Nreal δ (negSet Y) := by
    have h3 : negSet (negSet Y) = Y := by
      ext z
      simp only [negSet, Set.mem_image]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        simpa using hw
      · intro hz
        exact ⟨-z, ⟨z, hz, by simp⟩, by simp⟩
    have h4 := covering_negation_le_two hδ h_negY_bdd
    rw [h3] at h4
    exact h4
  have h_eq1 : Set.image2 (· + ·) X (negSet Y) = Set.image2 (· - ·) X Y := by
    ext z
    simp only [negSet, Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨a, ha, c, hc, by ring⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, -b, ⟨b, hb, by ring⟩, by ring⟩
  have h_eq2 : Set.image2 (· + ·) Z (negSet Y) = Set.image2 (· - ·) Z Y := by
    ext z
    simp only [negSet, Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨a, ha, c, hc, by ring⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, -b, ⟨b, hb, by ring⟩, by ring⟩
  have h_rt_raw := discretized_ruzsa_triangle hδ hX hZ h_negY_bdd h_negY_nonempty
  have h_comm : Set.image2 (· + ·) (negSet Y) Z = Set.image2 (· + ·) Z (negSet Y) := by
    ext z
    simp only [Set.mem_image2]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b, hb, a, ha, by ring⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b, hb, a, ha, by ring⟩
  have h_rt : Nreal δ (Set.image2 (· - ·) X Z) * Nreal δ (negSet Y) ≤
      9 * Nreal δ (Set.image2 (· - ·) X Y) * Nreal δ (Set.image2 (· - ·) Z Y) := by
    rw [h_eq1, h_comm, h_eq2] at h_rt_raw
    exact h_rt_raw
  have h_eq3 : Set.image2 (· - ·) Z Y = negSet (Set.image2 (· - ·) Y Z) := by
    ext z
    simp only [negSet, Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b - a, ⟨b, hb, a, ha, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨a, ha, b, hb, h_eq⟩, rfl⟩
      exact ⟨b, hb, a, ha, by linarith⟩
  have h_negZY : Nreal δ (Set.image2 (· - ·) Z Y) ≤
      2 * Nreal δ (Set.image2 (· - ·) Y Z) := by
    rw [h_eq3]
    exact covering_negation_le_two hδ (bounded_image2_sub hY hZ)
  calc Nreal δ (Set.image2 (· - ·) X Z) * Nreal δ Y
    ≤ Nreal δ (Set.image2 (· - ·) X Z) * (2 * Nreal δ (negSet Y)) := by gcongr
  _ = 2 * (Nreal δ (Set.image2 (· - ·) X Z) * Nreal δ (negSet Y)) := by ring
  _ ≤ 2 * (9 * Nreal δ (Set.image2 (· - ·) X Y) * Nreal δ (Set.image2 (· - ·) Z Y)) := by
      gcongr <;> exact h_rt
  _ = 18 * Nreal δ (Set.image2 (· - ·) X Y) * Nreal δ (Set.image2 (· - ·) Z Y) := by ring
  _ ≤ 18 * Nreal δ (Set.image2 (· - ·) X Y) * (2 * Nreal δ (Set.image2 (· - ·) Y Z)) := by gcongr
  _ = 36 * Nreal δ (Set.image2 (· - ·) X Y) * Nreal δ (Set.image2 (· - ·) Y Z) := by ring

/-! ### 3. Scale-down upper bound -/

/-- `N(r·S) ≤ 2·N(S)` for `0 < r ≤ 1`. -/
lemma covering_scale_down_le_two {δ r : ℝ} (hδ : 0 < δ) (hr_pos : 0 < r)
    (hr_le_one : r ≤ 1) {S : Set ℝ} (hS : Bornology.IsBounded S) :
    Nreal δ (scaleSet r S) ≤ 2 * Nreal δ S := by
  let IrS := (realCubeIndexSet_finite hδ (scaleSet_bounded (t := r) (A := S) hS)).toFinset
  let IS := (realCubeIndexSet_finite hδ hS).toFinset
  have hIrS : (IrS : Set ℤ) = realCubeIndexSet δ (scaleSet r S) := Set.Finite.coe_toFinset _
  have hIS : (IS : Set ℤ) = realCubeIndexSet δ S := Set.Finite.coe_toFinset _
  have h_exists : ∀ (j : ℤ), j ∈ IrS → ∃ (k : ℤ), k ∈ IS ∧
      (r : ℝ) * (k : ℝ) - 1 < (j : ℝ) ∧ (j : ℝ) < (r : ℝ) * ((k : ℝ) + 1) := by
    intro j hj
    have h_j_in : (j : ℤ) ∈ (↑IrS : Set ℤ) := hj
    have hj' : (Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) ∩ scaleSet r S).Nonempty := by
      rw [hIrS] at h_j_in
      exact h_j_in
    rcases hj' with ⟨y, ⟨hy1, hy2⟩, hyS⟩
    rcases hyS with ⟨x, hxS, rfl⟩
    let k : ℤ := Int.floor (x / δ)
    have hk1 : δ * (k : ℝ) ≤ x := by
      have h : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hk2 : x < δ * ((k : ℝ) + 1) := by
      have h : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hkS : k ∈ realCubeIndexSet δ S := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨x, ?_⟩
      exact ⟨⟨hk1, hk2⟩, hxS⟩
    have h_j1 : (r : ℝ) * (k : ℝ) - 1 < (j : ℝ) := by
      have h9 : r * (δ * (k : ℝ)) ≤ r * x := mul_le_mul_of_nonneg_left hk1 (by linarith)
      have h10 : r * x < δ * ((j : ℝ) + 1) := hy2
      have h11 : r * (δ * (k : ℝ)) < δ * ((j : ℝ) + 1) := by linarith
      have h12 : r * (k : ℝ) < (j : ℝ) + 1 := by
        have h13 : r * (δ * (k : ℝ)) = δ * (r * (k : ℝ)) := by ring
        rw [h13] at h11
        nlinarith
      linarith
    have h_j2 : (j : ℝ) < (r : ℝ) * ((k : ℝ) + 1) := by
      have h9 : δ * (j : ℝ) ≤ r * x := hy1
      have h10 : r * x < r * (δ * ((k : ℝ) + 1)) := mul_lt_mul_of_pos_left hk2 hr_pos
      have h11 : δ * (j : ℝ) < r * (δ * ((k : ℝ) + 1)) := by linarith
      have h12 : (j : ℝ) < r * ((k : ℝ) + 1) := by
        have h13 : r * (δ * ((k : ℝ) + 1)) = δ * (r * ((k : ℝ) + 1)) := by ring
        rw [h13] at h11
        nlinarith
      exact h12
    have h_k_in : k ∈ IS := by
      have h : k ∈ (↑IS : Set ℤ) := by
        rw [hIS]
        exact hkS
      exact_mod_cast h
    exact ⟨k, h_k_in, h_j1, h_j2⟩
  classical
  let f : ℤ → ℤ := fun j =>
    if h : j ∈ IrS then (h_exists j h).choose else 0
  have h_f : ∀ j ∈ IrS, f j ∈ IS ∧
      (r : ℝ) * ((f j : ℝ)) - 1 < (j : ℝ) ∧ (j : ℝ) < (r : ℝ) * (((f j : ℝ)) + 1) := by
    intro j hj
    have h10 : f j = (h_exists j hj).choose := by
      simp only [f]
      rw [dif_pos hj]
    rw [h10]
    exact (h_exists j hj).choose_spec
  have h_maps_to : ∀ j ∈ IrS, f j ∈ IS := fun j hj => (h_f j hj).1
  have h_fiber : ∀ k ∈ IS, (Finset.filter (fun j => f j = k) IrS).card ≤ 2 := by
    intro k _
    have h4 : ∀ j ∈ Finset.filter (fun j => f j = k) IrS,
        (r : ℝ) * (k : ℝ) - 1 < (j : ℝ) ∧ (j : ℝ) < (r : ℝ) * ((k : ℝ) + 1) := by
      intro j hj
      have h5 : j ∈ IrS := (Finset.mem_filter.mp hj).1
      have h6 : f j = k := (Finset.mem_filter.mp hj).2
      have h7 := (h_f j h5).2
      rw [h6] at h7
      exact h7
    let a := (r : ℝ) * (k : ℝ) - 1
    let b := (r : ℝ) * ((k : ℝ) + 1)
    have hlen : (b - a : ℝ) ≤ 2 := by
      dsimp only [a, b]
      have h : (r : ℝ) * ((k : ℝ) + 1) - ((r : ℝ) * (k : ℝ) - 1) = (r : ℝ) + 1 := by ring
      rw [h]
      linarith
    exact ints_in_open_interval_bound hlen h4
  have h_card : IrS.card ≤ 2 * IS.card :=
    Finset.card_le_mul_card_image_of_maps_to h_maps_to 2 h_fiber
  have hN_rS := realCoveringNumber_eq_card hδ (scaleSet_bounded (t := r) (A := S) hS)
  have hNS := realCoveringNumber_eq_card hδ hS
  dsimp only [Nreal] at *
  rw [hN_rS, hNS]
  have h_encard_rS : (realCubeIndexSet δ (scaleSet r S)).encard = IrS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (scaleSet_bounded (t := r) (A := S) hS))] <;> rfl
  have h_encard_S : (realCubeIndexSet δ S).encard = IS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hS)] <;> rfl
  rw [h_encard_rS, h_encard_S]
  norm_cast <;> exact_mod_cast h_card

/-! ### 4. Scale-down lower bound -/

/-- `N(S) ≤ (⌈1/c⌉+2)·N(r·S)` for `c ≤ r ≤ 1`. -/
lemma covering_scale_down_ge {δ r c : ℝ} (hδ : 0 < δ) (hc_pos : 0 < c)
    (hr_ge_c : c ≤ r) (hr_le_one : r ≤ 1) {S : Set ℝ} (hS : Bornology.IsBounded S) :
    Nreal δ S ≤ (Nat.ceil (1 / c) + 2 : ENNReal) * Nreal δ (scaleSet r S) := by
  let IS := (realCubeIndexSet_finite hδ hS).toFinset
  let IrS := (realCubeIndexSet_finite hδ (scaleSet_bounded (t := r) (A := S) hS)).toFinset
  have hIS : (IS : Set ℤ) = realCubeIndexSet δ S := Set.Finite.coe_toFinset _
  have hIrS : (IrS : Set ℤ) = realCubeIndexSet δ (scaleSet r S) := Set.Finite.coe_toFinset _
  let C : ℕ := Nat.ceil (1 / c) + 2
  have hr_pos : 0 < r := by linarith
  have h1r : 1 / r ≤ 1 / c := by gcongr
  have h_exists : ∀ (k : ℤ), k ∈ IS → ∃ (j : ℤ), j ∈ IrS ∧
      (j : ℝ) / r - 1 < (k : ℝ) ∧ (k : ℝ) < ((j : ℝ) + 1) / r := by
    intro k hk
    have h_k_in : (k : ℤ) ∈ (↑IS : Set ℤ) := hk
    have hk' : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty := by
      rw [hIS] at h_k_in
      exact h_k_in
    rcases hk' with ⟨x, ⟨hx1, hx2⟩, hxS⟩
    let y : ℝ := r * x
    have hyS : y ∈ scaleSet r S := ⟨x, hxS, rfl⟩
    let j : ℤ := Int.floor (y / δ)
    have hj1 : δ * (j : ℝ) ≤ y := by
      have h : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
      have h' : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
      have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj2 : y < δ * ((j : ℝ) + 1) := by
      have h : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
      have h' : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
      have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj_rS : j ∈ realCubeIndexSet δ (scaleSet r S) := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨y, ?_⟩
      exact ⟨⟨hj1, hj2⟩, hyS⟩
    have h_k1 : (j : ℝ) / r - 1 < (k : ℝ) := by
      have h9 : δ * (j : ℝ) ≤ r * x := hj1
      have h10 : r * x < r * (δ * ((k : ℝ) + 1)) := mul_lt_mul_of_pos_left hx2 hr_pos
      have h11 : δ * (j : ℝ) < r * (δ * ((k : ℝ) + 1)) := by linarith
      have h12 : (j : ℝ) < r * ((k : ℝ) + 1) := by
        have h13 : r * (δ * ((k : ℝ) + 1)) = δ * (r * ((k : ℝ) + 1)) := by ring
        rw [h13] at h11
        nlinarith
      have h14 : (j : ℝ) / r < (k : ℝ) + 1 := by
        calc (j : ℝ) / r
          < (r * ((k : ℝ) + 1)) / r := by gcongr
        _ = (k : ℝ) + 1 := by field_simp [hr_pos.ne'] <;> ring
      linarith
    have h_k2 : (k : ℝ) < ((j : ℝ) + 1) / r := by
      have h9 : r * (δ * (k : ℝ)) ≤ r * x := mul_le_mul_of_nonneg_left hx1 (by linarith)
      have h10 : r * x < δ * ((j : ℝ) + 1) := hj2
      have h11 : r * (δ * (k : ℝ)) < δ * ((j : ℝ) + 1) := by linarith
      have h12 : r * (k : ℝ) < (j : ℝ) + 1 := by
        have h13 : r * (δ * (k : ℝ)) = δ * (r * (k : ℝ)) := by ring
        rw [h13] at h11
        nlinarith
      have h14 : (k : ℝ) < ((j : ℝ) + 1) / r := by
        calc (k : ℝ)
          = (r * (k : ℝ)) / r := by field_simp [hr_pos.ne'] <;> ring
        _ < ((j : ℝ) + 1) / r := by gcongr
      exact h14
    have h_j_in : j ∈ IrS := by
      have h : j ∈ (↑IrS : Set ℤ) := by
        rw [hIrS]
        exact hj_rS
      exact_mod_cast h
    exact ⟨j, h_j_in, h_k1, h_k2⟩
  classical
  let f : ℤ → ℤ := fun k =>
    if h : k ∈ IS then (h_exists k h).choose else 0
  have h_f : ∀ k ∈ IS, f k ∈ IrS ∧
      ((f k : ℝ)) / r - 1 < (k : ℝ) ∧ (k : ℝ) < (((f k : ℝ)) + 1) / r := by
    intro k hk
    have h10 : f k = (h_exists k hk).choose := by
      simp only [f]
      rw [dif_pos hk]
    rw [h10]
    exact (h_exists k hk).choose_spec
  have h_maps_to : ∀ k ∈ IS, f k ∈ IrS := fun k hk => (h_f k hk).1
  have h_fiber : ∀ j ∈ IrS, (Finset.filter (fun k => f k = j) IS).card ≤ C := by
    intro j _
    have h4 : ∀ k ∈ Finset.filter (fun k => f k = j) IS,
        (j : ℝ) / r - 1 < (k : ℝ) ∧ (k : ℝ) < ((j : ℝ) + 1) / r := by
      intro k hk
      have h5 : k ∈ IS := (Finset.mem_filter.mp hk).1
      have h6 : f k = j := (Finset.mem_filter.mp hk).2
      have h7 := (h_f k h5).2
      rw [h6] at h7
      exact h7
    let a := (j : ℝ) / r - 1
    let b := ((j : ℝ) + 1) / r
    have hlen : (b - a : ℝ) ≤ (C : ℝ) := by
      dsimp only [a, b, C]
      have h : ((j : ℝ) + 1) / r - ((j : ℝ) / r - 1) = 1 / r + 1 := by
        field_simp [hr_pos.ne'] <;> ring
      rw [h]
      have h2 : 1 / r + 1 ≤ (Nat.ceil (1 / c) : ℝ) + 2 := by
        have h3 : 1 / r ≤ 1 / c := h1r
        have h4 : 1 / c ≤ (Nat.ceil (1 / c) : ℝ) := Nat.le_ceil _
        linarith
      simpa [Nat.cast_add] using h2
    exact ints_in_open_interval_bound hlen h4
  have h_card : IS.card ≤ C * IrS.card :=
    Finset.card_le_mul_card_image_of_maps_to h_maps_to C h_fiber
  have hN_rS := realCoveringNumber_eq_card hδ (scaleSet_bounded (t := r) (A := S) hS)
  have hNS := realCoveringNumber_eq_card hδ hS
  dsimp only [Nreal] at *
  rw [hNS, hN_rS]
  have h_encard_S : (realCubeIndexSet δ S).encard = IS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hS)] <;> rfl
  have h_encard_rS : (realCubeIndexSet δ (scaleSet r S)).encard = IrS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (scaleSet_bounded (t := r) (A := S) hS))] <;> rfl
  rw [h_encard_S, h_encard_rS]
  have h_main : (IS.card : ENNReal) ≤ (C : ENNReal) * (IrS.card : ENNReal) := by
    exact_mod_cast h_card
  simpa [C] using h_main

/-! ### 5. Scaling and coarsening -/

/-- Scaling identity: `N(δ, t·A) = N(δ/t, A)`. -/
lemma covering_scaling {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    {A : Set ℝ} (hA : Bornology.IsBounded A) :
    Nreal δ (scaleSet t A) = Nreal (δ / t) A := by
  have h_eq : realCubeIndexSet δ (scaleSet t A) = realCubeIndexSet (δ / t) A := by
    ext k
    simp only [realCubeIndexSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨⟨h1, h2⟩, ⟨x, hxA, rfl⟩⟩⟩
      refine ⟨x, ?_⟩
      exact ⟨⟨by
        calc (δ / t) * (k : ℝ) = (δ * (k : ℝ)) / t := by field_simp [ht.ne'] <;> ring
          _ ≤ (t * x) / t := by gcongr
          _ = x := by field_simp [ht.ne'] <;> ring,
        by
          calc x = (t * x) / t := by field_simp [ht.ne'] <;> ring
          _ < (δ * ((k : ℝ) + 1)) / t := by gcongr
          _ = (δ / t) * ((k : ℝ) + 1) := by field_simp [ht.ne'] <;> ring⟩, hxA⟩
    · rintro ⟨x, ⟨⟨h1, h2⟩, hxA⟩⟩
      refine ⟨t * x, ?_⟩
      exact ⟨⟨by
        calc δ * (k : ℝ) = t * ((δ / t) * (k : ℝ)) := by field_simp [ht.ne'] <;> ring
          _ ≤ t * x := by gcongr,
        by
          calc t * x < t * ((δ / t) * ((k : ℝ) + 1)) := by gcongr
          _ = δ * ((k : ℝ) + 1) := by field_simp [ht.ne'] <;> ring⟩, ⟨x, hxA, rfl⟩⟩
  have h_bdd1 : Bornology.IsBounded (scaleSet t A) := scaleSet_bounded hA
  have h_eq1 : Nreal δ (scaleSet t A) = ENat.toENNReal (realCubeIndexSet δ (scaleSet t A)).encard := by
    have h := realCoveringNumber_eq_card hδ h_bdd1
    simpa [Nreal] using h
  have h_eq2 : Nreal (δ / t) A = ENat.toENNReal (realCubeIndexSet (δ / t) A).encard := by
    have h := realCoveringNumber_eq_card (div_pos hδ ht) hA
    simpa [Nreal] using h
  rw [h_eq1, h_eq2, h_eq]

/-- Coarsening: `N(δ, A) ≥ (t/3)·N(δ·t, A)` for `0 < t ≤ 1`. -/
lemma covering_coarsening {δ t : ℝ} (hδ : 0 < δ) (ht_pos : 0 < t) (ht_le_one : t ≤ 1)
    {A : Set ℝ} (hA : Bornology.IsBounded A) :
    ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤ Nreal δ A := by
  let ItA := (realCubeIndexSet_finite (mul_pos hδ ht_pos) hA).toFinset
  let IA := (realCubeIndexSet_finite hδ hA).toFinset
  have hItA : (ItA : Set ℤ) = realCubeIndexSet (δ * t) A := Set.Finite.coe_toFinset _
  have hIA : (IA : Set ℤ) = realCubeIndexSet δ A := Set.Finite.coe_toFinset _
  let C : ℕ := Nat.floor (1 / t + 1) + 1
  have hC_le : (C : ℝ) ≤ 3 / t := by
    dsimp only [C]
    have h1 : (Nat.floor (1 / t + 1) : ℝ) ≤ 1 / t + 1 := Nat.floor_le (by positivity)
    have h2 : (2 : ℝ) ≤ 2 / t := by
      have h3 : 0 < t := ht_pos
      have h4 : t ≤ 1 := ht_le_one
      calc (2 : ℝ) = 2 / 1 := by norm_num
        _ ≤ 2 / t := by gcongr
    have h5 : 1 / t + 2 ≤ 3 / t := by
      have h6 : 1 / t + 2 ≤ 1 / t + 2 / t := by gcongr
      have h7 : 1 / t + 2 / t = 3 / t := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
    have hC_eq : ((Nat.floor (1 / t + 1) + 1 : ℕ) : ℝ) = (Nat.floor (1 / t + 1) : ℝ) + 1 := by
      simp [Nat.cast_add] <;> ring
    rw [hC_eq]
    linarith
  have h_exists : ∀ (j : ℤ), j ∈ ItA → ∃ (k : ℤ), k ∈ IA ∧
      (k : ℝ) ∈ Set.Ioo ((j : ℝ) * t - 1) ((j : ℝ) * t + t) := by
    intro j hj
    have h_j_in : (j : ℤ) ∈ (↑ItA : Set ℤ) := hj
    have hj' : (Set.Ico ((δ * t) * (j : ℝ)) ((δ * t) * ((j : ℝ) + 1)) ∩ A).Nonempty := by
      rw [hItA] at h_j_in
      exact h_j_in
    rcases hj' with ⟨x, ⟨hx1, hx2⟩, hxA⟩
    let k : ℤ := Int.floor (x / δ)
    have hk1 : δ * (k : ℝ) ≤ x := by
      have h : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hk2 : x < δ * ((k : ℝ) + 1) := by
      have h : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hkA : k ∈ realCubeIndexSet δ A := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨x, ?_⟩
      exact ⟨⟨hk1, hk2⟩, hxA⟩
    have h_k1 : (j : ℝ) * t - 1 < (k : ℝ) := by
      have h9 : (δ * t) * (j : ℝ) ≤ x := hx1
      have h10 : x < δ * ((k : ℝ) + 1) := hk2
      have h11 : (δ * t) * (j : ℝ) < δ * ((k : ℝ) + 1) := by linarith
      have h12 : t * (j : ℝ) < (k : ℝ) + 1 := by
        have h13 : (δ * t) * (j : ℝ) = δ * (t * (j : ℝ)) := by ring
        rw [h13] at h11
        nlinarith
      linarith
    have h_k2 : (k : ℝ) < (j : ℝ) * t + t := by
      have h9 : δ * (k : ℝ) ≤ x := hk1
      have h10 : x < (δ * t) * ((j : ℝ) + 1) := hx2
      have h11 : δ * (k : ℝ) < (δ * t) * ((j : ℝ) + 1) := by linarith
      have h12 : (k : ℝ) < t * ((j : ℝ) + 1) := by
        have h13 : (δ * t) * ((j : ℝ) + 1) = δ * (t * ((j : ℝ) + 1)) := by ring
        rw [h13] at h11
        nlinarith
      have h14 : t * ((j : ℝ) + 1) = (j : ℝ) * t + t := by ring
      rw [h14] at h12
      exact h12
    have h_k_in : k ∈ IA := by
      have h : k ∈ (↑IA : Set ℤ) := by
        rw [hIA]
        exact hkA
      exact_mod_cast h
    exact ⟨k, h_k_in, ⟨h_k1, h_k2⟩⟩
  classical
  let f : ℤ → ℤ := fun j =>
    if h : j ∈ ItA then (h_exists j h).choose else 0
  have h_f : ∀ j ∈ ItA, f j ∈ IA ∧
      (f j : ℝ) ∈ Set.Ioo ((j : ℝ) * t - 1) ((j : ℝ) * t + t) := by
    intro j hj
    have h10 : f j = (h_exists j hj).choose := by
      simp only [f]
      rw [dif_pos hj]
    rw [h10]
    exact (h_exists j hj).choose_spec
  have h_maps_to : ∀ j ∈ ItA, f j ∈ IA := fun j hj => (h_f j hj).1
  have h_fiber : ∀ k ∈ IA, (Finset.filter (fun j => f j = k) ItA).card ≤ C := by
    intro k _
    have h4 : ∀ j ∈ Finset.filter (fun j => f j = k) ItA,
        (j : ℝ) * t - 1 < (k : ℝ) ∧ (k : ℝ) < (j : ℝ) * t + t := by
      intro j hj
      have h5 : j ∈ ItA := (Finset.mem_filter.mp hj).1
      have h6 : f j = k := (Finset.mem_filter.mp hj).2
      have h7 := (h_f j h5).2
      rw [h6] at h7
      exact h7
    let a := (k : ℝ) / t - 1
    let b := ((k : ℝ) + 1) / t
    have h5 : ∀ j ∈ Finset.filter (fun j => f j = k) ItA, (a : ℝ) < (j : ℝ) ∧ (j : ℝ) < (b : ℝ) := by
      intro j hj
      have h6 := h4 j hj
      have h7 : a < (j : ℝ) := by
        dsimp only [a]
        have h8 : (k : ℝ) < (j : ℝ) * t + t := h6.2
        have h9 : (k : ℝ) / t - 1 < (j : ℝ) := by
          have h10 : (k : ℝ) < t * ((j : ℝ) + 1) := by
            have h11 : (j : ℝ) * t + t = t * ((j : ℝ) + 1) := by ring
            rw [h11] at h8
            exact h8
          calc (k : ℝ) / t - 1
            = ((k : ℝ) - t) / t := by field_simp [ht_pos.ne'] <;> ring
          _ < (t * ((j : ℝ) + 1) - t) / t := by gcongr
          _ = (j : ℝ) := by field_simp [ht_pos.ne'] <;> ring
        exact h9
      have h8 : (j : ℝ) < b := by
        dsimp only [b]
        have h9 : (j : ℝ) * t - 1 < (k : ℝ) := h6.1
        have h10 : (j : ℝ) < ((k : ℝ) + 1) / t := by
          have h11 : (j : ℝ) * t < (k : ℝ) + 1 := by linarith
          calc (j : ℝ)
            = ((j : ℝ) * t) / t := by field_simp [ht_pos.ne'] <;> ring
          _ < ((k : ℝ) + 1) / t := by gcongr
        exact h10
      exact ⟨h7, h8⟩
    have hlen : (b - a : ℝ) ≤ (C : ℝ) := by
      dsimp only [a, b, C]
      have h : ((k : ℝ) + 1) / t - ((k : ℝ) / t - 1) = 1 / t + 1 := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h]
      have h2 : 1 / t + 1 ≤ (Nat.floor (1 / t + 1) : ℝ) + 1 := by
        have h3 : (1 / t + 1 : ℝ) < (Nat.floor (1 / t + 1) : ℝ) + 1 := Nat.lt_floor_add_one (1 / t + 1)
        linarith
      simpa [Nat.cast_add] using h2
    exact ints_in_open_interval_bound hlen h5
  have h_card : ItA.card ≤ C * IA.card :=
    Finset.card_le_mul_card_image_of_maps_to h_maps_to C h_fiber
  have hN_ItA := realCoveringNumber_eq_card (mul_pos hδ ht_pos) hA
  have hN_IA := realCoveringNumber_eq_card hδ hA
  dsimp only [Nreal] at *
  rw [hN_ItA, hN_IA]
  have h_encard_ItA : (realCubeIndexSet (δ * t) A).encard = ItA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite (mul_pos hδ ht_pos) hA)] <;> rfl
  have h_encard_IA : (realCubeIndexSet δ A).encard = IA.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hA)] <;> rfl
  rw [h_encard_ItA, h_encard_IA]
  have h_main : (ItA.card : ENNReal) ≤ (C : ENNReal) * (IA.card : ENNReal) := by
    exact_mod_cast h_card
  have hC_le' : (C : ENNReal) ≤ ENNReal.ofReal (3 / t) := by
    have h_pos : 0 ≤ 3 / t := by positivity
    have hC_nat : (C : ENNReal) = ENNReal.ofReal (C : ℝ) := by
      simp
    rw [hC_nat]
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr hC_le
  have h_final : (ItA.card : ENNReal) ≤ ENNReal.ofReal (3 / t) * (IA.card : ENNReal) := by
    calc (ItA.card : ENNReal)
      ≤ (C : ENNReal) * (IA.card : ENNReal) := h_main
    _ ≤ ENNReal.ofReal (3 / t) * (IA.card : ENNReal) := by gcongr
  have h_mul : ENNReal.ofReal (t / 3) * ENNReal.ofReal (3 / t) = 1 := by
    have h1 : 0 ≤ t / 3 := by positivity
    have h2 : 0 ≤ 3 / t := by positivity
    rw [← ENNReal.ofReal_mul h1]
    have h3 : (t / 3) * (3 / t) = 1 := by
      field_simp [ht_pos.ne'] <;> ring
    rw [h3] <;> simp
  calc ENNReal.ofReal (t / 3) * (ItA.card : ENNReal)
    ≤ ENNReal.ofReal (t / 3) * (ENNReal.ofReal (3 / t) * (IA.card : ENNReal)) := by gcongr
  _ = (ENNReal.ofReal (t / 3) * ENNReal.ofReal (3 / t)) * (IA.card : ENNReal) := by ring
  _ = 1 * (IA.card : ENNReal) := by rw [h_mul]
  _ = (IA.card : ENNReal) := by ring

/-- `N(A) ≥ (δ^c/3)·N(t⁻¹A)` for `δ^c ≤ t ≤ 1`. -/
lemma covering_NA_ge_NB {δ t c : ℝ} (hδ : 0 < δ) (hc_pos : 0 < c)
    (ht_pos : 0 < t) (ht_le_one : t ≤ 1) (h_t_lower : δ ^ c ≤ t)
    {A : Set ℝ} (hA : Bornology.IsBounded A) :
    ENNReal.ofReal (δ ^ c / 3) * Nreal δ (scaleSet t⁻¹ A) ≤ Nreal δ A := by
  have h_scaling : Nreal δ (scaleSet t⁻¹ A) = Nreal (δ * t) A := by
    have h1 : Nreal δ (scaleSet t⁻¹ A) = Nreal (δ / t⁻¹) A :=
      covering_scaling hδ (by positivity) hA
    have h2 : δ / t⁻¹ = δ * t := by
      field_simp [ht_pos.ne'] <;> ring
    rw [h1, h2]
  rw [h_scaling]
  have h_coarse : ENNReal.ofReal (t / 3) * Nreal (δ * t) A ≤ Nreal δ A :=
    covering_coarsening hδ ht_pos ht_le_one hA
  have h_real : (δ ^ c / 3 : ℝ) ≤ t / 3 := by
    have h : δ ^ c ≤ t := h_t_lower
    gcongr
  calc ENNReal.ofReal (δ ^ c / 3) * Nreal (δ * t) A
    ≤ ENNReal.ofReal (t / 3) * Nreal (δ * t) A := by gcongr
  _ ≤ Nreal δ A := h_coarse

/-! ### 6. Sumset trivial bound -/

/-- `N(X+Y) ≤ 4·N(X)·N(Y)`. -/
lemma covering_sumset_trivial {δ : ℝ} (hδ : 0 < δ) {X Y : Set ℝ}
    (hX : Bornology.IsBounded X) (hY : Bornology.IsBounded Y) :
    Nreal δ (Set.image2 (· + ·) X Y) ≤ 4 * Nreal δ X * Nreal δ Y := by
  let IX := (realCubeIndexSet_finite hδ hX).toFinset
  let IY := (realCubeIndexSet_finite hδ hY).toFinset
  let IXY := (realCubeIndexSet_finite hδ (bounded_image2_add hX hY)).toFinset
  have hIX : (IX : Set ℤ) = realCubeIndexSet δ X := Set.Finite.coe_toFinset _
  have hIY : (IY : Set ℤ) = realCubeIndexSet δ Y := Set.Finite.coe_toFinset _
  have hIXY : (IXY : Set ℤ) = realCubeIndexSet δ (Set.image2 (· + ·) X Y) := Set.Finite.coe_toFinset _
  have h_incl : IXY ⊆ (IX + IY) + ({0, 1} : Finset ℤ) := by
    intro k hk
    have h_k_in : (k : ℤ) ∈ (↑IXY : Set ℤ) := hk
    have hk' : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ Set.image2 (· + ·) X Y).Nonempty := by
      rw [hIXY] at h_k_in
      exact h_k_in
    rcases hk' with ⟨z, ⟨hz1, hz2⟩, hzS⟩
    rcases hzS with ⟨x, hxX, y, hyY, h_eq⟩
    let i : ℤ := Int.floor (x / δ)
    let j : ℤ := Int.floor (y / δ)
    have hi1 : δ * (i : ℝ) ≤ x := by
      have h : (i : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (i : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hi2 : x < δ * ((i : ℝ) + 1) := by
      have h : x / δ < (i : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((i : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj1 : δ * (j : ℝ) ≤ y := by
      have h : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
      have h' : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
      have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj2 : y < δ * ((j : ℝ) + 1) := by
      have h : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
      have h' : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
      have h'' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hiX : i ∈ realCubeIndexSet δ X := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨x, ?_⟩
      exact ⟨⟨hi1, hi2⟩, hxX⟩
    have hjY : j ∈ realCubeIndexSet δ Y := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      refine ⟨y, ?_⟩
      exact ⟨⟨hj1, hj2⟩, hyY⟩
    have h_i_in : i ∈ IX := by
      have h : i ∈ (↑IX : Set ℤ) := by rw [hIX]; exact hiX
      exact_mod_cast h
    have h_j_in : j ∈ IY := by
      have h : j ∈ (↑IY : Set ℤ) := by rw [hIY]; exact hjY
      exact_mod_cast h
    have h_ij_in : i + j ∈ IX + IY := Finset.mem_add.mpr ⟨i, h_i_in, j, h_j_in, rfl⟩
    have h_k1 : (i : ℝ) + (j : ℝ) ≤ (k : ℝ) := by
      have h1 : δ * ((i : ℝ) + (j : ℝ)) ≤ x + y := by linarith
      have h2 : x + y = z := h_eq
      have h3 : δ * ((i : ℝ) + (j : ℝ)) < δ * ((k : ℝ) + 1) := by
        rw [h2] at h1
        linarith [hz2]
      have h4 : (i : ℝ) + (j : ℝ) < (k : ℝ) + 1 := by nlinarith
      have h5 : (i + j : ℤ) < k + 1 := by
        have h6 : ((i + j : ℤ) : ℝ) = (i : ℝ) + (j : ℝ) := by simp
        have h7 : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by simp
        have h8 : ((i + j : ℤ) : ℝ) < ((k + 1 : ℤ) : ℝ) := by
          rw [h6, h7]
          exact h4
        exact_mod_cast h8
      have h8 : i + j ≤ k := by omega
      exact_mod_cast h8
    have h_k2 : (k : ℝ) ≤ (i : ℝ) + (j : ℝ) + 1 := by
      have h1 : x + y < δ * (((i : ℝ) + (j : ℝ)) + 2) := by linarith
      have h2 : x + y = z := h_eq
      have h3 : δ * (k : ℝ) < δ * (((i : ℝ) + (j : ℝ)) + 2) := by
        rw [h2] at h1
        linarith [hz1]
      have h4 : (k : ℝ) < (i : ℝ) + (j : ℝ) + 2 := by nlinarith
      have h5 : (k : ℤ) < i + j + 2 := by
        have h6 : ((k : ℤ) : ℝ) = (k : ℝ) := by simp
        have h7 : (((i + j + 2 : ℤ)) : ℝ) = (i : ℝ) + (j : ℝ) + 2 := by simp
        have h8 : ((k : ℤ) : ℝ) < ((i + j + 2 : ℤ) : ℝ) := by
          rw [h6, h7]
          exact h4
        exact_mod_cast h8
      have h8 : k ≤ i + j + 1 := by omega
      exact_mod_cast h8
    have h_k3 : k = i + j ∨ k = i + j + 1 := by
      have h4 : i + j ≤ k := by exact_mod_cast h_k1
      have h5 : k ≤ i + j + 1 := by exact_mod_cast h_k2
      omega
    rcases h_k3 with (rfl | rfl)
    · have h6 : i + j ∈ (IX + IY) + ({0, 1} : Finset ℤ) := by
        exact Finset.mem_add.mpr ⟨i + j, h_ij_in, 0, by simp, by simp⟩
      exact h6
    · have h6 : i + j + 1 ∈ (IX + IY) + ({0, 1} : Finset ℤ) := by
        exact Finset.mem_add.mpr ⟨i + j, h_ij_in, 1, by simp, by simp⟩
      exact h6
  have h_card : IXY.card ≤ 2 * IX.card * IY.card := by
    have h1 : IXY.card ≤ ((IX + IY) + ({0, 1} : Finset ℤ)).card := Finset.card_le_card h_incl
    have h2 : ((IX + IY) + ({0, 1} : Finset ℤ)).card ≤ (IX + IY).card * 2 := by
      have h3 := Finset.card_add_le (s := IX + IY) (t := ({0, 1} : Finset ℤ))
      have h4 : ({0, 1} : Finset ℤ).card = 2 := by decide
      rw [h4] at h3
      <;> ring_nf at h3 ⊢ <;> exact h3
    have h4 : (IX + IY).card ≤ IX.card * IY.card := Finset.card_add_le
    calc IXY.card
      ≤ ((IX + IY) + ({0, 1} : Finset ℤ)).card := h1
    _ ≤ (IX + IY).card * 2 := h2
    _ ≤ IX.card * IY.card * 2 := by gcongr
    _ = 2 * IX.card * IY.card := by ring
  have hN_XY := realCoveringNumber_eq_card hδ (bounded_image2_add hX hY)
  have hN_X := realCoveringNumber_eq_card hδ hX
  have hN_Y := realCoveringNumber_eq_card hδ hY
  dsimp only [Nreal] at *
  rw [hN_XY, hN_X, hN_Y]
  have h_encard_XY : (realCubeIndexSet δ (Set.image2 (· + ·) X Y)).encard = IXY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ (bounded_image2_add hX hY))] <;> rfl
  have h_encard_X : (realCubeIndexSet δ X).encard = IX.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hX)] <;> rfl
  have h_encard_Y : (realCubeIndexSet δ Y).encard = IY.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hY)] <;> rfl
  rw [h_encard_XY, h_encard_X, h_encard_Y]
  norm_cast
  <;> exact_mod_cast (by linarith)

end

end WeakTwoEndsSumProduct
