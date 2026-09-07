module

/-
# Finset → Set Transfer for Kaufman Energy

Transfers `IsRealDeltaSet` from a finite δ-dense subset `P_fin` to the full
set `P`, via projection density and covering-number comparison.

## Proof route

1. **Projection density**: If `P_fin` is δ-dense in `P` (sup norm), then for
   θ ∈ [0,1], `affineProjection θ P_fin` is 2δ-dense in `affineProjection θ P`.

2. **Covering comparison**: If every point of `B` is within 2δ of `A`, then
   `Nreal δ B ≤ 5 * Nreal δ A`.
   - Cube-index map: each cube meeting B maps to a cube meeting A
   - Index distance ≤ 2, so fibers ≤ 5

3. **Delta-set transfer**: If `A` is a `(δ, κ, C)`-set and `B` is a 2δ-dense
   superset of `A`, then `B` is a `(δ, κ, 25*C)`-set.
   - For each dyadic r-cube `Q`, enlarge by 2δ → covered by ≤5 r-cubes `Q_i`
   - `N(B ∩ Q) ≤ 5 * N(A ∩ Q') ≤ 5 * Σ N(A ∩ Q_i) ≤ 25 * C * N(A) * r^κ`
   - Since `A ⊆ B`, `N(A) ≤ N(B)`, giving `N(B ∩ Q) ≤ 25*C * N(B) * r^κ`

4. **Main transfer**: Apply to each θ in the good set Θ.

## Whiteprint node
`robust_projection/EnergyTransfer`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.DiscretizedBourgainAveraging
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Finset Set Bornology Classical
open bourgain_projection_theorem

namespace robust_projection

/-- Sup-norm δ-density: every point of P is within δ (per coordinate) of P_fin. -/
def IsDeltaDense (δ : ℝ)
    (P_fin : Finset (EuclideanSpace ℝ (Fin 2)))
    (P : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (↑P_fin : Set (EuclideanSpace ℝ (Fin 2))) ⊆ P ∧
  ∀ p ∈ P, ∃ p_fin ∈ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2))), ∀ i : Fin 2, |p i - p_fin i| ≤ δ

/-- Projection preserves density: for θ ∈ [0,1], π_θ(P_fin) is 2δ-dense
    in π_θ(P). -/
lemma projection_density
    {δ : ℝ} (hδ : 0 < δ)
    {P_fin : Finset (EuclideanSpace ℝ (Fin 2))}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {θ : ℝ} (hθ1 : 0 ≤ θ) (hθ2 : θ ≤ 1)
    (h_dense : IsDeltaDense δ P_fin P) :
    ∀ x ∈ affineProjection θ P,
      ∃ y ∈ affineProjection θ (↑P_fin), |x - y| ≤ 2 * δ := by
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  have h1 : ∃ p_fin ∈ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2))), ∀ i : Fin 2, |p i - p_fin i| ≤ δ :=
    h_dense.2 p hp
  rcases h1 with ⟨p_fin, hpf, hdist⟩
  let y : ℝ := p_fin 0 * θ + p_fin 1
  have hy_in : y ∈ affineProjection θ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2))) :=
    ⟨p_fin, hpf, rfl⟩
  have h_bound : |(p 0 * θ + p 1) - y| ≤ 2 * δ := by
    dsimp only [y]
    have h1 : |(p 0 * θ + p 1) - (p_fin 0 * θ + p_fin 1)| =
        |(p 0 - p_fin 0) * θ + (p 1 - p_fin 1)| := by ring_nf
    rw [h1]
    have h2 : |(p 0 - p_fin 0) * θ + (p 1 - p_fin 1)| ≤
        |(p 0 - p_fin 0) * θ| + |p 1 - p_fin 1| := by
      exact abs_add_le ((p 0 - p_fin 0) * θ) (p 1 - p_fin 1)
    have h3 : |(p 0 - p_fin 0) * θ| ≤ δ := by
      have h4 : |(p 0 - p_fin 0) * θ| = |p 0 - p_fin 0| * |θ| := by
        rw [abs_mul]
      rw [h4]
      have h5 : |p 0 - p_fin 0| ≤ δ := hdist 0
      have h6 : |θ| ≤ 1 := by
        rw [abs_le] <;> constructor <;> linarith
      calc
        |p 0 - p_fin 0| * |θ| ≤ δ * |θ| := by gcongr
        _ ≤ δ * 1 := by gcongr
        _ = δ := by ring
    have h4 : |p 1 - p_fin 1| ≤ δ := hdist 1
    linarith
  exact ⟨y, hy_in, h_bound⟩

/-- General covering number comparison: if every point of B is within 2δ of
    some point of A (no subset requirement), then
    `Nreal δ B ≤ 5 * Nreal δ A`. -/
lemma dense_covering_number_le_general
    {δ : ℝ} (hδ : 0 < δ)
    {A B : Set ℝ}
    (hA_bdd : Bornology.IsBounded A)
    (hB_bdd : Bornology.IsBounded B)
    (h_dense : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ 2 * δ) :
    Nreal δ B ≤ ENNReal.ofReal (5 : ℝ) * Nreal δ A := by
  classical
  let h_fin_B : (realCubeIndexSet δ B).Finite := realCubeIndexSet_finite hδ hB_bdd
  let h_fin_A : (realCubeIndexSet δ A).Finite := realCubeIndexSet_finite hδ hA_bdd
  let K_B : Finset ℤ := h_fin_B.toFinset
  let K_A : Finset ℤ := h_fin_A.toFinset
  have hK_B_def : ∀ k, k ∈ K_B ↔ k ∈ realCubeIndexSet δ B := by
    intro k; exact Set.Finite.mem_toFinset h_fin_B
  have hK_A_def : ∀ k, k ∈ K_A ↔ k ∈ realCubeIndexSet δ A := by
    intro k; exact Set.Finite.mem_toFinset h_fin_A
  have h_exists : ∀ k ∈ K_B, ∃ m : ℤ, m ∈ K_A ∧ |k - m| ≤ 2 := by
    intro k hk
    have hk' : k ∈ realCubeIndexSet δ B := (hK_B_def k).mp hk
    rcases hk' with ⟨x, hxI, hxB⟩
    rcases h_dense x hxB with ⟨y, hyA, hxy⟩
    let m : ℤ := Int.floor (y / δ)
    have hyI : y ∈ Set.Ico (δ * (m : ℝ)) (δ * ((m : ℝ) + 1)) := by
      have h4 : (m : ℝ) ≤ y / δ := Int.floor_le (y / δ)
      have h5 : y / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
      constructor
      · calc y = δ * (y / δ) := by field_simp [hδ.ne'] <;> ring
        _ ≥ δ * (m : ℝ) := by gcongr
      · calc y = δ * (y / δ) := by field_simp [hδ.ne'] <;> ring
        _ < δ * ((m : ℝ) + 1) := by gcongr
    have hmK_A : m ∈ K_A := by
      rw [hK_A_def m]
      simp [realCubeIndexSet, Set.mem_setOf_eq] <;> exact ⟨y, hyI, hyA⟩
    have hkm : |k - m| ≤ 2 := by
      have h_upper : k - m ≤ 2 := by
        by_contra h
        have h' : k - m ≥ 3 := by linarith
        have h4 : (k : ℝ) - (m : ℝ) ≥ 3 := by exact_mod_cast h'
        have h5 : x - y > 2 * δ := by
          have h6 : x ≥ δ * (k : ℝ) := hxI.1
          have h7 : y < δ * ((m : ℝ) + 1) := hyI.2
          have h8 : x - y > δ * ((k : ℝ) - (m : ℝ) - 1) := by linarith
          have h9 : (k : ℝ) - (m : ℝ) - 1 ≥ 2 := by linarith
          have h10 : δ * ((k : ℝ) - (m : ℝ) - 1) ≥ δ * 2 := by gcongr
          linarith
        have h11 : |x - y| > 2 * δ := by
          have h12 : x - y > 0 := by linarith
          have h13 : |x - y| = x - y := abs_of_pos h12
          rw [h13]; exact h5
        have h14 : |x - y| ≤ 2 * δ := hxy
        linarith
      have h_lower : m - k ≤ 2 := by
        by_contra h
        have h' : m - k ≥ 3 := by linarith
        have h4 : (m : ℝ) - (k : ℝ) ≥ 3 := by exact_mod_cast h'
        have h5 : y - x > 2 * δ := by
          have h6 : y ≥ δ * (m : ℝ) := hyI.1
          have h7 : x < δ * ((k : ℝ) + 1) := hxI.2
          have h8 : y - x > δ * ((m : ℝ) - (k : ℝ) - 1) := by linarith
          have h9 : (m : ℝ) - (k : ℝ) - 1 ≥ 2 := by linarith
          have h10 : δ * ((m : ℝ) - (k : ℝ) - 1) ≥ δ * 2 := by gcongr
          linarith
        have h11 : |x - y| > 2 * δ := by
          have h12 : y - x > 0 := by linarith
          have h13 : |x - y| = y - x := by
            have h14 : x - y < 0 := by linarith
            rw [abs_of_neg h14] <;> linarith
          rw [h13]; exact h5
        have h14 : |x - y| ≤ 2 * δ := hxy
        linarith
      rw [abs_le] <;> constructor <;> linarith
    exact ⟨m, hmK_A, hkm⟩
  let f : ℤ → ℤ := fun k => if h : k ∈ K_B then Classical.choose (h_exists k h) else 0
  have h_f_mem : ∀ k ∈ K_B, f k ∈ K_A := by
    intro k hk
    have h_f_def : f k = Classical.choose (h_exists k hk) := by
      simp [f, hk]
    rw [h_f_def]
    exact (Classical.choose_spec (h_exists k hk)).1
  have h_f_bound : ∀ k ∈ K_B, |k - f k| ≤ 2 := by
    intro k hk
    have h_f_def : f k = Classical.choose (h_exists k hk) := by
      simp [f, hk]
    rw [h_f_def]
    exact (Classical.choose_spec (h_exists k hk)).2
  have h_fiber : ∀ m ∈ K_A, (K_B.filter (fun k => f k = m)).card ≤ 5 := by
    intro m _
    have h3 : ∀ k ∈ K_B.filter (fun k => f k = m), |k - m| ≤ 2 := by
      intro k hk
      have h4 : k ∈ K_B := (Finset.mem_filter.mp hk).1
      have h5 : f k = m := (Finset.mem_filter.mp hk).2
      have h6 : |k - f k| ≤ 2 := h_f_bound k h4
      rw [h5] at h6; exact h6
    let S : Finset ℤ := Finset.Icc (m - 2) (m + 2)
    have h4 : K_B.filter (fun k => f k = m) ⊆ S := by
      intro k hk
      have h5 : |k - m| ≤ 2 := h3 k hk
      have h6 : m - 2 ≤ k := by linarith [abs_le.mp h5]
      have h7 : k ≤ m + 2 := by linarith [abs_le.mp h5]
      simp only [S, Finset.mem_Icc] <;> omega
    have h5 : (K_B.filter (fun k => f k = m)).card ≤ S.card := Finset.card_le_card h4
    have h6 : S.card = 5 := by
      simp [S, Finset.Icc_eq_empty_of_lt]
      <;> norm_num <;> omega
    rw [h6] at h5; exact h5
  have h_main : K_B.card ≤ 5 * K_A.card :=
    finset_card_le_mul_of_bounded_fibers f h_f_mem h_fiber
  have hN_B : Nreal δ B = ENat.toENNReal (K_B.card : ENat) := by
    have h2 : Nreal δ B = ENat.toENNReal (realCubeIndexSet δ B).encard :=
      realCoveringNumber_eq_card hδ hB_bdd
    have h3 : (realCubeIndexSet δ B).encard = (K_B.card : ENat) :=
      Set.Finite.encard_eq_coe_toFinset_card h_fin_B
    rw [h2, h3]
  have hN_A : Nreal δ A = ENat.toENNReal (K_A.card : ENat) := by
    have h2 : Nreal δ A = ENat.toENNReal (realCubeIndexSet δ A).encard :=
      realCoveringNumber_eq_card hδ hA_bdd
    have h3 : (realCubeIndexSet δ A).encard = (K_A.card : ENat) :=
      Set.Finite.encard_eq_coe_toFinset_card h_fin_A
    rw [h2, h3]
  rw [hN_B, hN_A]
  have h_final : ENat.toENNReal (K_B.card : ENat) ≤
      ENNReal.ofReal (5 : ℝ) * ENat.toENNReal (K_A.card : ENat) := by
    have h : (K_B.card : ENat) ≤ (5 * K_A.card : ENat) := by exact_mod_cast h_main
    have h' : ENat.toENNReal (K_B.card : ENat) ≤ ENat.toENNReal ((5 * K_A.card : ENat)) :=
      ENat.toENNReal_mono h
    have h'' : ENat.toENNReal ((5 * K_A.card : ENat)) =
        ENNReal.ofReal (5 : ℝ) * ENat.toENNReal (K_A.card : ENat) := by
      simp [Nat.cast_mul] <;> ring
    rw [h''] at h'; exact h'
  exact h_final

/-- Covering number comparison: if A ⊆ B and A is 2δ-dense in B,
    then Nreal δ B ≤ 5 * Nreal δ A. -/
lemma dense_covering_number_le
    {δ : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {A B : Set ℝ} (hA_sub_B : A ⊆ B)
    (hB_bdd : Bornology.IsBounded B)
    (h_dense : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ 2 * δ) :
    Nreal δ B ≤ ENNReal.ofReal (5 : ℝ) * Nreal δ A := by
  have hA_bdd : Bornology.IsBounded A := hB_bdd.subset hA_sub_B
  exact dense_covering_number_le_general hδ hA_bdd hB_bdd h_dense

/-- Helper: if `realLineCopy A` is bounded, then `A` is bounded. -/
lemma bounded_of_realLineCopy {A : Set ℝ}
    (h : Bornology.IsBounded (realLineCopy A)) : Bornology.IsBounded A := by
  have h1 : A = (fun x : EuclideanSpace ℝ (Fin 1) => x 0) '' realLineCopy A := by
    ext y
    simp only [realLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hy
      refine ⟨mkPoint1 y, ?_, rfl⟩
      simpa [mkPoint1] using hy
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [h1]
  have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
    intro x y
    have h := PiLp.edist_apply_le x y 0
    simpa using h
  exact h_lip.isBounded_image h

/-- Helper: if `realLineCopy A` is nonempty, then `A` is nonempty. -/
lemma nonempty_of_realLineCopy {A : Set ℝ}
    (h : (realLineCopy A).Nonempty) : A.Nonempty := by
  rcases h with ⟨x, hx⟩
  exact ⟨x 0, hx⟩

/-- Delta-set transfer from dense subset to superset.

If A is a (δ, κ, C)-delta-set and B is a 2δ-dense superset of A,
then B is a (δ, κ, 25*C)-delta-set. -/
lemma is_real_delta_set_of_dense_superset
    {δ κ C : ℝ} {A B : Set ℝ}
    (hA_sub_B : A ⊆ B)
    (hA : IsRealDeltaSet δ κ C A)
    (h_dense : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ 2 * δ)
    (hB_bdd : Bornology.IsBounded B)
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) :
    IsRealDeltaSet δ κ (25 * C) B := by
  rcases hA with ⟨hA_bdd_real, hA_nonempty_real, _, _, _, hκ_nonneg, hκ_le_one, hC_pos, hA_delta⟩
  have hA_bdd : Bornology.IsBounded A := bounded_of_realLineCopy hA_bdd_real
  have hA_nonempty : A.Nonempty := nonempty_of_realLineCopy hA_nonempty_real
  have hB_nonempty : B.Nonempty := hA_nonempty.mono hA_sub_B
  have hB_bdd_real : Bornology.IsBounded (realLineCopy B) := by
    have h1 : realLineCopy B = (fun y : ℝ => mkPoint1 y) '' B := by
      ext z
      simp [realLineCopy, mkPoint1, Set.mem_image]
      <;> constructor
      · intro hz; exact ⟨z 0, hz, by ext i; fin_cases i; rfl⟩
      · rintro ⟨y, hy, rfl⟩; simpa [mkPoint1] using hy
    rw [h1]
    have h_lip : LipschitzWith 1 (fun y : ℝ => mkPoint1 y) := by
      apply LipschitzWith.of_dist_le_mul
      intro y1 y2
      have h_eq : dist (mkPoint1 y1) (mkPoint1 y2) = dist y1 y2 := by
        have h1 : mkPoint1 y1 - mkPoint1 y2 = mkPoint1 (y1 - y2) := by
          ext i; fin_cases i <;> simp [mkPoint1]
        have h2 : ‖mkPoint1 (y1 - y2)‖ = |y1 - y2| := by
          have h3 : ‖mkPoint1 (y1 - y2)‖ ^ 2 = (y1 - y2) ^ 2 := by
            have h4 : ‖mkPoint1 (y1 - y2)‖ ^ 2 = ∑ i : Fin 1, |(mkPoint1 (y1 - y2)) i| ^ 2 := by exact EuclideanSpace.norm_sq_eq (mkPoint1 (y1 - y2))
            rw [h4]
            simp [Fin.sum_univ_one, mkPoint1]
            <;> ring
          have h4 : 0 ≤ ‖mkPoint1 (y1 - y2)‖ := by positivity
          have h5 : 0 ≤ |y1 - y2| := by positivity
          have h6 : |y1 - y2| ^ 2 = (y1 - y2) ^ 2 := by
            rw [sq_abs]
          nlinarith
        have h5 : dist (mkPoint1 y1) (mkPoint1 y2) = ‖mkPoint1 y1 - mkPoint1 y2‖ := by
          rw [dist_eq_norm]
        rw [h5, h1, h2]
        <;> rfl
      rw [h_eq] <;> simp
    exact h_lip.isBounded_image hB_bdd
  have h25C_pos : 0 < 25 * C := by positivity
  have hB_nonempty_real : (realLineCopy B).Nonempty := by
    rcases hB_nonempty with ⟨b, hb⟩
    exact ⟨mkPoint1 b, by simpa [realLineCopy, mkPoint1] using hb⟩
  refine' ⟨hB_bdd_real, hB_nonempty_real, by norm_num, hδ_dyadic, hδ, hκ_nonneg, hκ_le_one, h25C_pos, _⟩
  intro r Q hr_dyadic hQ_cube hδ_le_r hr_le_one
  rcases hQ_cube with ⟨k, rfl⟩
  let k0 : ℤ := k 0
  let I : Set ℝ := Set.Ico (r * (k0 : ℝ)) (r * ((k0 : ℝ) + 1))
  have hr_pos : 0 < r := lt_of_lt_of_le hδ hδ_le_r
  have hQ_eq : dyadicCube r k = realLineCopy I := by
    ext x
    simp only [realLineCopy, dyadicCube, I, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · intro h; exact h 0
    · intro h; intro i; fin_cases i; exact h
  have h_inter_B : realLineCopy B ∩ dyadicCube r k = realLineCopy (B ∩ I) := by
    rw [hQ_eq]
    ext x
    simp [realLineCopy, Set.mem_inter_iff] <;> tauto
  have h_inter_A : ∀ (j : ℤ), realLineCopy A ∩ dyadicCube r (fun (_ : Fin 1) => j) =
      realLineCopy (A ∩ Set.Ico (r * (j : ℝ)) (r * ((j : ℝ) + 1))) := by
    intro j
    ext x
    simp only [realLineCopy, dyadicCube, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 0⟩
    · rintro ⟨h1, h2⟩
      constructor
      · exact h1
      · intro i; fin_cases i; exact h2
  let I' : Set ℝ := Set.Ico (r * ((k0 - 2 : ℤ) : ℝ)) (r * ((k0 + 3 : ℤ) : ℝ))
  have hI'_sub : I' ⊆ ⋃ j ∈ Finset.Icc (k0 - 2) (k0 + 2),
      Set.Ico (r * (j : ℝ)) (r * ((j : ℝ) + 1)) := by
    intro x hx
    have h1 : r * ((k0 - 2 : ℤ) : ℝ) ≤ x := hx.1
    have h2 : x < r * ((k0 + 3 : ℤ) : ℝ) := hx.2
    let j : ℤ := Int.floor (x / r)
    have hj1 : r * (j : ℝ) ≤ x := by
      have h3 : (j : ℝ) ≤ x / r := Int.floor_le (x / r)
      have h4 : r * (j : ℝ) ≤ r * (x / r) := by gcongr
      have h5 : r * (x / r) = x := by field_simp [hr_pos.ne'] <;> ring
      rw [h5] at h4; exact h4
    have hj2 : x < r * ((j : ℝ) + 1) := by
      have h3 : x / r < (j : ℝ) + 1 := Int.lt_floor_add_one (x / r)
      calc x = r * (x / r) := by field_simp [hr_pos.ne'] <;> ring
        _ < r * ((j : ℝ) + 1) := by gcongr
    have hj3 : k0 - 2 ≤ j := by
      have h4 : ((k0 - 2 : ℤ) : ℝ) ≤ x / r := by
        calc ((k0 - 2 : ℤ) : ℝ)
          = (r * ((k0 - 2 : ℤ) : ℝ)) / r := by field_simp [hr_pos.ne'] <;> ring
        _ ≤ x / r := by gcongr
      exact Int.le_floor.mpr h4
    have hj4 : j ≤ k0 + 2 := by
      have h4 : x / r < ((k0 + 3 : ℤ) : ℝ) := by
        calc x / r < (r * ((k0 + 3 : ℤ) : ℝ)) / r := by gcongr
          _ = ((k0 + 3 : ℤ) : ℝ) := by field_simp [hr_pos.ne'] <;> ring
      have h5 : j < (k0 + 3 : ℤ) := Int.floor_lt.mpr h4
      omega
    have h_j_in : j ∈ Finset.Icc (k0 - 2) (k0 + 2) := by
      rw [Finset.mem_Icc]
      exact ⟨hj3, hj4⟩
    have h_x_in : x ∈ Set.Ico (r * (j : ℝ)) (r * ((j : ℝ) + 1)) := ⟨hj1, hj2⟩
    have h12 : ∃ (i : ℤ), r * (i : ℝ) ≤ x ∧ (k0 ≤ i + 2 ∧ i ≤ k0 + 2) ∧ x < r * ((i : ℝ) + 1) :=
      ⟨j, hj1, by omega, hj2⟩
    have h_goal : x ∈ ⋃ j ∈ Finset.Icc (k0 - 2) (k0 + 2), Set.Ico (r * (j : ℝ)) (r * ((j : ℝ) + 1)) := by
      simpa using h12
    exact h_goal
  have h_dense' : ∀ x ∈ B ∩ I, ∃ y ∈ A ∩ I', |x - y| ≤ 2 * δ := by
    intro x hx
    have hxB : x ∈ B := hx.1
    have hxI : x ∈ I := hx.2
    rcases h_dense x hxB with ⟨y, hyA, hxy⟩
    have h_y_in_I' : y ∈ I' := by
      simp only [I', Set.mem_Ico]
      have h1 : r * ((k0 - 2 : ℤ) : ℝ) ≤ y := by
        have h2 : r * (k0 : ℝ) ≤ x := hxI.1
        have h3 : x - y ≤ 2 * δ := by
          have h4 : |x - y| ≤ 2 * δ := hxy
          have h5 : x - y ≤ |x - y| := le_abs_self (x - y)
          linarith
        have h6 : 2 * δ ≤ 2 * r := by gcongr <;> linarith
        have h_eq1 : r * ((k0 - 2 : ℤ) : ℝ) = r * (k0 : ℝ) - 2 * r := by
          simp [Int.cast_sub] <;> ring
        rw [h_eq1]
        linarith
      have h2 : y < r * ((k0 + 3 : ℤ) : ℝ) := by
        have h3 : x < r * ((k0 : ℝ) + 1) := hxI.2
        have h4 : y - x ≤ 2 * δ := by
          have h5 : |x - y| ≤ 2 * δ := hxy
          have h6 : y - x ≤ |x - y| := by
            have h7 : |y - x| = |x - y| := by rw [show y - x = -(x - y) by ring, abs_neg]
            have h8 : y - x ≤ |y - x| := le_abs_self (y - x)
            rw [h7] at h8; exact h8
          linarith
        have h7 : 2 * δ ≤ 2 * r := by gcongr <;> linarith
        have h_eq2 : r * ((k0 : ℝ) + 1) + 2 * r = r * ((k0 + 3 : ℤ) : ℝ) := by
          simp [Int.cast_add] <;> ring
        calc y ≤ x + 2 * δ := by linarith
          _ ≤ x + 2 * r := by gcongr <;> linarith
          _ < r * ((k0 : ℝ) + 1) + 2 * r := by linarith
          _ = r * ((k0 + 3 : ℤ) : ℝ) := h_eq2
      exact ⟨h1, h2⟩
    exact ⟨y, ⟨hyA, h_y_in_I'⟩, hxy⟩
  have hB_I_bdd : Bornology.IsBounded (B ∩ I) := hB_bdd.subset Set.inter_subset_left
  have hA_I'_bdd : Bornology.IsBounded (A ∩ I') := hA_bdd.subset Set.inter_subset_left
  have h1 : Nreal δ (B ∩ I) ≤ ENNReal.ofReal (5 : ℝ) * Nreal δ (A ∩ I') :=
    dense_covering_number_le_general hδ hA_I'_bdd hB_I_bdd h_dense'
  let S_j : ℤ → Set ℝ := fun j => Set.Ico (r * (j : ℝ)) (r * ((j : ℝ) + 1))
  let F : Finset ℤ := Finset.Icc (k0 - 2) (k0 + 2)
  have h2 : Nreal δ (A ∩ I') ≤ ∑ j ∈ F, Nreal δ (A ∩ S_j j) := by
    have h_sub1 : A ∩ I' ⊆ ⋃ j ∈ F, A ∩ S_j j := by
      intro x hx
      have h_x_in_I' : x ∈ I' := hx.2
      have h : x ∈ ⋃ j ∈ F, S_j j := hI'_sub h_x_in_I'
      have h' : ∃ (j : ℤ), j ∈ F ∧ x ∈ S_j j := by simpa using h
      rcases h' with ⟨j, hj, hxj⟩
      have h_final : x ∈ A ∧ ∃ (i : ℤ), i ∈ F ∧ x ∈ S_j i :=
        ⟨hx.1, j, hj, hxj⟩
      have h_goal : x ∈ ⋃ j ∈ F, A ∩ S_j j := by simpa using h_final
      exact h_goal
    have h_sub1' : realLineCopy (A ∩ I') ⊆ realLineCopy (⋃ j ∈ F, A ∩ S_j j) := by
      intro x hx
      have h9 : x 0 ∈ A ∩ I' := by simpa [realLineCopy] using hx
      have h10 : x 0 ∈ ⋃ j ∈ F, A ∩ S_j j := h_sub1 h9
      simpa [realLineCopy] using h10
    have h_mono : Nreal δ (A ∩ I') ≤ Nreal δ (⋃ j ∈ F, A ∩ S_j j) :=
      ENat.toENNReal_mono (dyadicCoveringNumber_mono h_sub1')
    have h_realLineCopy_union : realLineCopy (⋃ j ∈ F, A ∩ S_j j) =
        ⋃ j ∈ F, realLineCopy (A ∩ S_j j) := by
      ext z
      simp [realLineCopy, Set.mem_iUnion] <;> tauto
    have h_subadd : Nreal δ (⋃ j ∈ F, A ∩ S_j j) ≤ ∑ j ∈ F, Nreal δ (A ∩ S_j j) := by
      simp only [Nreal, h_realLineCopy_union]
      have h3 : dyadicCubesMeeting δ (⋃ j ∈ F, realLineCopy (A ∩ S_j j)) ⊆
          ⋃ j ∈ F, dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j)) := by
        intro Q hQ
        rcases hQ with ⟨hQ_cube, ⟨z, hzQ, hzU⟩⟩
        have hzU' : ∃ (j : ℤ), j ∈ F ∧ z ∈ realLineCopy (A ∩ S_j j) := by
          have hzAnd : z 0 ∈ A ∧ ∃ (x : ℤ), x ∈ F ∧ z 0 ∈ S_j x := by
            simpa [realLineCopy, Set.mem_iUnion] using hzU
          rcases hzAnd with ⟨hA, ⟨j, hjF, hSj⟩⟩
          refine ⟨j, hjF, ?_⟩
          simpa [realLineCopy] using ⟨hA, hSj⟩
        rcases hzU' with ⟨j, hj, hzj⟩
        have h_Q_in : Q ∈ dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j)) := ⟨hQ_cube, ⟨z, hzQ, hzj⟩⟩
        have h_goal : ∃ (i : ℤ), i ∈ F ∧ Q ∈ dyadicCubesMeeting δ (realLineCopy (A ∩ S_j i)) := ⟨j, hj, h_Q_in⟩
        have h_final : Q ∈ ⋃ j ∈ F, dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j)) := by simpa using h_goal
        exact h_final
      have h4 : dyadicCoveringNumber δ (⋃ j ∈ F, realLineCopy (A ∩ S_j j)) ≤
          ∑ j ∈ F, dyadicCoveringNumber δ (realLineCopy (A ∩ S_j j)) := by
        simp only [dyadicCoveringNumber]
        calc
          (dyadicCubesMeeting δ (⋃ j ∈ F, realLineCopy (A ∩ S_j j))).encard
            ≤ (⋃ j ∈ F, dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j))).encard := Set.encard_mono h3
          _ ≤ ∑ j ∈ F, (dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j))).encard :=
            Finset.set_encard_biUnion_le F (fun j => dyadicCubesMeeting δ (realLineCopy (A ∩ S_j j)))
      let h_hom : ENat →+ ENNReal :=
        { toFun := ENat.toENNReal,
          map_zero' := by simp,
          map_add' := by intro x y; simp [ENat.toENNReal_add] }
      have h5 : ENat.toENNReal (∑ j ∈ F, dyadicCoveringNumber δ (realLineCopy (A ∩ S_j j))) =
          ∑ j ∈ F, ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (A ∩ S_j j))) :=
        map_sum h_hom (fun j => dyadicCoveringNumber δ (realLineCopy (A ∩ S_j j))) F
      have h6 : ENat.toENNReal (dyadicCoveringNumber δ (⋃ j ∈ F, realLineCopy (A ∩ S_j j))) ≤
          ENat.toENNReal (∑ j ∈ F, dyadicCoveringNumber δ (realLineCopy (A ∩ S_j j))) :=
        ENat.toENNReal_mono h4
      rw [h5] at h6
      exact h6
    exact le_trans h_mono h_subadd
  have h3 : ∀ j ∈ F, Nreal δ (A ∩ S_j j) ≤
      ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ) := by
    intro j _
    let Q_j : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r (fun (_ : Fin 1) => j)
    have hQ_j : Q_j ∈ dyadicCubes 1 r := by
      simp [Q_j, dyadicCubes] <;> exact ⟨(fun _ => j), rfl⟩
    have h4 : realLineCopy A ∩ Q_j = realLineCopy (A ∩ S_j j) := h_inter_A j
    have h5 := hA_delta (r := r) (Q := Q_j) hr_dyadic hQ_j hδ_le_r hr_le_one
    simpa [Nreal, h4] using h5
  have h4 : ∑ j ∈ F, Nreal δ (A ∩ S_j j) ≤
      ENNReal.ofReal (5 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) := by
    have h5 : ∑ j ∈ F, Nreal δ (A ∩ S_j j) ≤
        ∑ j ∈ F, (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) :=
      Finset.sum_le_sum h3
    have h6 : F.card = 5 := by
      simp [F, Finset.Icc_eq_empty_of_lt] <;> norm_num <;> omega
    rw [Finset.sum_const, h6] at h5
    simpa [mul_assoc] using h5
  have h5 : Nreal δ (B ∩ I) ≤
      ENNReal.ofReal (25 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) := by
    calc
      Nreal δ (B ∩ I) ≤ ENNReal.ofReal (5 : ℝ) * Nreal δ (A ∩ I') := h1
      _ ≤ ENNReal.ofReal (5 : ℝ) * (∑ j ∈ F, Nreal δ (A ∩ S_j j)) := by gcongr
      _ ≤ ENNReal.ofReal (5 : ℝ) * (ENNReal.ofReal (5 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ))) := by gcongr
      _ = ENNReal.ofReal (25 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have h6 : Nreal δ A ≤ Nreal δ B := by
    have h7 : realLineCopy A ⊆ realLineCopy B := by
      intro x hx
      simpa [realLineCopy] using hA_sub_B (by simpa [realLineCopy] using hx)
    exact ENat.toENNReal_mono (dyadicCoveringNumber_mono h7)
  have h7 : ENNReal.ofReal (25 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) ≤
      ENNReal.ofReal (25 * C) * Nreal δ B * ENNReal.ofReal (r ^ κ) := by
    have h8 : ENNReal.ofReal (25 : ℝ) * ENNReal.ofReal C = ENNReal.ofReal (25 * C) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h9 : ENNReal.ofReal (25 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ)) =
        (ENNReal.ofReal (25 : ℝ) * ENNReal.ofReal C) * Nreal δ A * ENNReal.ofReal (r ^ κ) := by ring
    calc
      ENNReal.ofReal (25 : ℝ) * (ENNReal.ofReal C * Nreal δ A * ENNReal.ofReal (r ^ κ))
        = (ENNReal.ofReal (25 : ℝ) * ENNReal.ofReal C) * Nreal δ A * ENNReal.ofReal (r ^ κ) := h9
      _ = ENNReal.ofReal (25 * C) * Nreal δ A * ENNReal.ofReal (r ^ κ) := by rw [h8] <;> ring
      _ ≤ ENNReal.ofReal (25 * C) * Nreal δ B * ENNReal.ofReal (r ^ κ) := by
          gcongr <;> exact h6
  have h_final : Nreal δ (B ∩ I) ≤
      ENNReal.ofReal (25 * C) * Nreal δ B * ENNReal.ofReal (r ^ κ) :=
    le_trans h5 h7
  simpa [Nreal, h_inter_B] using h_final

/-- Transfer IsRealDeltaSet from π_θ(P_fin) to π_θ(P) for a single θ. -/
lemma single_direction_transfer
    {δ κ C'' : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {P_fin : Finset (EuclideanSpace ℝ (Fin 2))}
    {θ : ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hθ1 : 0 ≤ θ) (hθ2 : θ ≤ 1)
    (hP_bdd : Bornology.IsBounded P)
    (hP_fin_dense : IsDeltaDense δ P_fin P)
    (h_fin_reg : IsRealDeltaSet δ κ C'' (affineProjection θ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2))))) :
    IsRealDeltaSet δ κ (25 * C'') (affineProjection θ P) := by
  let A := affineProjection θ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2)))
  let B := affineProjection θ P
  have h_sub : A ⊆ B := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, hP_fin_dense.1 hp, rfl⟩
  have h_dense : ∀ x ∈ B, ∃ y ∈ A, |x - y| ≤ 2 * δ :=
    projection_density hδ hθ1 hθ2 hP_fin_dense
  have hB_bdd : Bornology.IsBounded B := by
    let f : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ :=
      { toFun := fun p => p 0 * θ + p 1,
        map_add' := by
          intro p q
          have h1 : (p + q) 0 = p 0 + q 0 := by simp
          have h2 : (p + q) 1 = p 1 + q 1 := by simp
          rw [h1, h2] <;> ring,
        map_smul' := by
          intro c p
          have h1 : (c • p) 0 = c * p 0 := by simp
          have h2 : (c • p) 1 = c * p 1 := by simp
          simp [h1, h2, mul_comm c] <;> ring,
        cont := by fun_prop }
    exact Bornology.IsBounded.image f hP_bdd
  exact is_real_delta_set_of_dense_superset h_sub h_fin_reg h_dense hB_bdd hδ hδ_dyadic

/-- Finset → Set transfer for Kaufman energy.

Given that projections of P_fin are delta-sets for a set Θ of directions
with μ Θ > 1/2, and P_fin is δ-dense in P, transfer the delta-set property
to projections of P for (a subset of) Θ with μ Θ > 1/3.

In fact the same Θ works, giving μ Θ > 1/2 > 1/3. -/
lemma kaufman_transfer_set
    {δ s τ κ C C' C'' : ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {P_fin : Finset (EuclideanSpace ℝ (Fin 2))}
    {μ : Measure ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hP_bdd : Bornology.IsBounded P)
    (hP_nonempty : P.Nonempty)
    (hP_reg : IsDeltaSCSet δ (2 * s) C P)
    (hμ_frost : IsDirectionFrostman δ τ C' μ)
    (h_main : ∃ (Θ : Set ℝ), μ Θ > 1 / 2 ∧ ∀ θ ∈ Θ,
       IsRealDeltaSet δ (κ / 2) C'' (affineProjection θ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2)))))
    (hP_fin_dense : IsDeltaDense δ P_fin P) :
    ∃ (Θ : Set ℝ), μ Θ > 1 / 3 ∧ ∀ θ ∈ Θ,
      IsRealDeltaSet δ (κ / 2) (25 * C'') (affineProjection θ P) := by
  rcases h_main with ⟨Θ, hμΘ, hΘ_reg⟩
  let Θ' := Θ ∩ μ.support
  have hμΘ' : μ Θ' = μ Θ := by
    have h_null : μ (μ.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
    have h2 : Θ \ μ.support ⊆ μ.supportᶜ := by
      intro x hx
      simpa [Set.mem_compl_iff] using hx.2
    have h3 : μ (Θ \ μ.support) = 0 := measure_mono_null h2 h_null
    have h4 : μ Θ ≤ μ Θ' + μ (Θ \ μ.support) := by
      have h5 : Θ ⊆ Θ' ∪ (Θ \ μ.support) := by
        intro x hx
        by_cases h6 : x ∈ μ.support
        · exact Or.inl ⟨hx, h6⟩
        · exact Or.inr ⟨hx, h6⟩
      have h7 : μ Θ ≤ μ (Θ' ∪ (Θ \ μ.support)) := measure_mono h5
      have h8 : μ (Θ' ∪ (Θ \ μ.support)) ≤ μ Θ' + μ (Θ \ μ.support) := measure_union_le _ _
      exact le_trans h7 h8
    have h9 : μ Θ' ≤ μ Θ := measure_mono (show Θ' ⊆ Θ from Set.inter_subset_left)
    rw [h3] at h4
    have h10 : μ Θ ≤ μ Θ' := by simpa using h4
    exact le_antisymm h9 h10
  have hμΘ'_gt : μ Θ' > 1 / 2 := by
    rw [hμΘ'] <;> exact hμΘ
  have h_θ_in_01 : ∀ θ ∈ Θ', 0 ≤ θ ∧ θ ≤ 1 := by
    intro θ hθ
    have hθ_supp : θ ∈ μ.support := hθ.2
    have h : θ ∈ Set.Icc (0 : ℝ) 1 := hμ_frost.2.1 hθ_supp
    exact ⟨h.1, h.2⟩
  have h_transfer : ∀ θ ∈ Θ',
      IsRealDeltaSet δ (κ / 2) (25 * C'') (affineProjection θ P) := by
    intro θ hθ
    have hθ1 : 0 ≤ θ := (h_θ_in_01 θ hθ).1
    have hθ2 : θ ≤ 1 := (h_θ_in_01 θ hθ).2
    have h_fin_reg : IsRealDeltaSet δ (κ / 2) C''
        (affineProjection θ (↑P_fin : Set (EuclideanSpace ℝ (Fin 2)))) := hΘ_reg θ hθ.1
    exact single_direction_transfer hδ hδ_dyadic hθ1 hθ2 hP_bdd hP_fin_dense h_fin_reg
  have hμΘ_third : μ Θ' > 1 / 3 := by
    have h1 : (1 / 3 : ENNReal) < (1 / 2 : ENNReal) := by norm_num
    have h2 : (1 / 2 : ENNReal) < μ Θ' := hμΘ'_gt
    exact h1.trans h2
  exact ⟨Θ', hμΘ_third, h_transfer⟩

end robust_projection
