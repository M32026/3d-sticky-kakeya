module

/-
  Uniformity Bridge: multi_level_thin output → IsDyadicUniform

  Converts exact per-level branching counts from the thinning lemma
  into the IsDyadicUniform property required by multiscaleDecompKaufman.

  Uses base Δ = (1/2)^q for q > 0, with dyadic index map a(i) = q*i.
  The thinning loses density (48*log(1/Δ)/n)^n, which is small when
  q is chosen so that log(48*log(1/Δ))/log(1/Δ) is below the ε budget.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.BasicUniformization (parentBy)

namespace DiscretisedFurstenbergEstimate.Section9Bridge

open MultiscaleDecomposition

/-- Union of dyadic squares indexed by a finset. -/
def setFromIndicesMD (δ : ℝ) (S : Finset (ℤ × ℤ)) : Set EuclideanPlane :=
  ⋃ idx ∈ S, dyadicSquare δ idx.1 idx.2

/-! # Dyadic square nonemptiness -/

lemma dyadicSquare_nonempty {δ : ℝ} (hδ : 0 < δ) (c d : ℤ) :
    (dyadicSquare δ c d).Nonempty := by
  let f : Fin 2 → ℝ := fun i => if i = 0 then (c : ℝ) * δ else (d : ℝ) * δ
  let p : EuclideanPlane := WithLp.toLp (2 : ENNReal) f
  have h1 : p 0 = (c : ℝ) * δ := by simp [p, f] <;> aesop
  have h2 : p 1 = (d : ℝ) * δ := by simp [p, f] <;> aesop
  refine ⟨p, ?_⟩
  simp only [dyadicSquare, Set.mem_setOf_eq, h1, h2]
  constructor <;> constructor <;> linarith [hδ]

/-! # parentBy → square containment -/

/-- If `parentBy k (c,d) = (a,b)`, then the binary level-(m+k) square (c,d)
    is contained in the binary level-m square (a,b). -/
lemma parentBy_square_containment {m k : ℕ} (c d a b : ℤ)
    (h : parentBy k (c, d) = (a, b)) :
    dyadicSquare ((1 / 2 : ℝ) ^ (m + k)) c d ⊆
    dyadicSquare ((1 / 2 : ℝ) ^ m) a b := by
  have ha : c / (2 ^ k : ℤ) = a := by
    have h' := by simpa [parentBy, Prod.ext_iff] using h
    exact h'.1
  have hb : d / (2 ^ k : ℤ) = b := by
    have h' := by simpa [parentBy, Prod.ext_iff] using h
    exact h'.2
  have h_pos2k : 0 < (2 ^ k : ℤ) := by positivity
  have h1 : (a : ℝ) * (2 ^ k : ℝ) ≤ (c : ℝ) := by
    have h11 : (c / (2 ^ k : ℤ)) * (2 ^ k : ℤ) ≤ c := by
      have h_eq : c = (c / (2 ^ k : ℤ)) * (2 ^ k : ℤ) + c % (2 ^ k : ℤ) := by exact Eq.symm (Int.ediv_mul_add_emod c (2 ^ k))
      have h_nonneg : 0 ≤ c % (2 ^ k : ℤ) := Int.emod_nonneg _ (by positivity)
      linarith
    rw [ha] at h11; exact_mod_cast h11
  have h2 : c < (a + 1) * (2 ^ k : ℤ) := by
    have h21 : c % (2 ^ k : ℤ) < (2 ^ k : ℤ) := Int.emod_lt_of_pos _ h_pos2k
    have h22 : c = (c / (2 ^ k : ℤ)) * (2 ^ k : ℤ) + c % (2 ^ k : ℤ) := by exact Eq.symm (Int.ediv_mul_add_emod c (2 ^ k))
    have h23 : c = a * (2 ^ k : ℤ) + c % (2 ^ k : ℤ) := by
      rw [ha] at h22; exact h22
    linarith
  have h2' : (c : ℝ) < ((a : ℝ) + 1) * (2 ^ k : ℝ) := by exact_mod_cast h2
  have h3 : (b : ℝ) * (2 ^ k : ℝ) ≤ (d : ℝ) := by
    have h31 : (d / (2 ^ k : ℤ)) * (2 ^ k : ℤ) ≤ d := by
      have h_eq : d = (d / (2 ^ k : ℤ)) * (2 ^ k : ℤ) + d % (2 ^ k : ℤ) := by exact Eq.symm (Int.ediv_mul_add_emod d (2 ^ k))
      have h_nonneg : 0 ≤ d % (2 ^ k : ℤ) := Int.emod_nonneg _ (by positivity)
      linarith
    rw [hb] at h31; exact_mod_cast h31
  have h4 : d < (b + 1) * (2 ^ k : ℤ) := by
    have h41 : d % (2 ^ k : ℤ) < (2 ^ k : ℤ) := Int.emod_lt_of_pos _ h_pos2k
    have h42 : d = (d / (2 ^ k : ℤ)) * (2 ^ k : ℤ) + d % (2 ^ k : ℤ) := by exact Eq.symm (Int.ediv_mul_add_emod d (2 ^ k))
    have h43 : d = b * (2 ^ k : ℤ) + d % (2 ^ k : ℤ) := by
      rw [hb] at h42; exact h42
    linarith
  have h4' : (d : ℝ) < ((b : ℝ) + 1) * (2 ^ k : ℝ) := by exact_mod_cast h4
  have h_pow : (1 / 2 : ℝ) ^ k * (2 ^ k : ℝ) = 1 := by
    have h : (1 / 2 : ℝ) ^ k * (2 ^ k : ℝ) = ((1 / 2 : ℝ) * (2 : ℝ)) ^ k := by
      rw [←mul_pow]
    rw [h]
    norm_num
  have h_scale : (1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ) = (1 / 2 : ℝ) ^ m := by
    calc
      (1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ)
        = (1 / 2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ k * (2 ^ k : ℝ)) := by
          rw [pow_add] <;> ring
      _ = (1 / 2 : ℝ) ^ m * 1 := by rw [h_pow]
      _ = (1 / 2 : ℝ) ^ m := by ring
  intro x hx
  have hx1 : (c : ℝ) * (1 / 2 : ℝ) ^ (m + k) ≤ x 0 := hx.1.1
  have hx2 : x 0 < ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ (m + k) := hx.1.2
  have hx3 : (d : ℝ) * (1 / 2 : ℝ) ^ (m + k) ≤ x 1 := hx.2.1
  have hx4 : x 1 < ((d : ℝ) + 1) * (1 / 2 : ℝ) ^ (m + k) := hx.2.2
  have h5 : (a : ℝ) * (1 / 2 : ℝ) ^ m ≤ x 0 := by
    calc (a : ℝ) * (1 / 2 : ℝ) ^ m
      = (a : ℝ) * ((1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ)) := by rw [h_scale]
    _ = (a : ℝ) * (2 ^ k : ℝ) * (1 / 2 : ℝ) ^ (m + k) := by ring
    _ ≤ (c : ℝ) * (1 / 2 : ℝ) ^ (m + k) := by gcongr
    _ ≤ x 0 := hx1
  have h7 : x 0 < ((a : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by
    calc x 0
      < ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ (m + k) := hx2
    _ ≤ (((a : ℝ) + 1) * (2 ^ k : ℝ)) * (1 / 2 : ℝ) ^ (m + k) := by
      have h26 : (c : ℝ) + 1 ≤ ((a : ℝ) + 1) * (2 ^ k : ℝ) := by
        exact_mod_cast (show c + 1 ≤ (a + 1) * (2 ^ k : ℤ) from by omega)
      gcongr
    _ = ((a : ℝ) + 1) * ((1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ)) := by ring
    _ = ((a : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by rw [h_scale]
  have h9 : (b : ℝ) * (1 / 2 : ℝ) ^ m ≤ x 1 := by
    calc (b : ℝ) * (1 / 2 : ℝ) ^ m
      = (b : ℝ) * ((1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ)) := by rw [h_scale]
    _ = (b : ℝ) * (2 ^ k : ℝ) * (1 / 2 : ℝ) ^ (m + k) := by ring
    _ ≤ (d : ℝ) * (1 / 2 : ℝ) ^ (m + k) := by gcongr
    _ ≤ x 1 := hx3
  have h11 : x 1 < ((b : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by
    calc x 1
      < ((d : ℝ) + 1) * (1 / 2 : ℝ) ^ (m + k) := hx4
    _ ≤ (((b : ℝ) + 1) * (2 ^ k : ℝ)) * (1 / 2 : ℝ) ^ (m + k) := by
      have h46 : (d : ℝ) + 1 ≤ ((b : ℝ) + 1) * (2 ^ k : ℝ) := by
        exact_mod_cast (show d + 1 ≤ (b + 1) * (2 ^ k : ℤ) from by omega)
      gcongr
    _ = ((b : ℝ) + 1) * ((1 / 2 : ℝ) ^ (m + k) * (2 ^ k : ℝ)) := by ring
    _ = ((b : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by rw [h_scale]
  exact ⟨⟨h5, h7⟩, ⟨h9, h11⟩⟩

/-! # Dyadic square injectivity -/

lemma dyadicSquare_inj {δ : ℝ} (hδ : 0 < δ) {i1 j1 i2 j2 : ℤ}
    (h : dyadicSquare δ i1 j1 = dyadicSquare δ i2 j2) : i1 = i2 ∧ j1 = j2 := by
  rcases dyadicSquare_nonempty hδ i1 j1 with ⟨x, hx⟩
  have hx' : x ∈ dyadicSquare δ i2 j2 := by rw [h] at hx; exact hx
  have h_i1_lt : (i1 : ℝ) < (i2 : ℝ) + 1 := by
    have h : (i1 : ℝ) * δ < ((i2 : ℝ) + 1) * δ := lt_of_le_of_lt hx.1.1 hx'.1.2
    nlinarith
  have h_i2_lt : (i2 : ℝ) < (i1 : ℝ) + 1 := by
    have h : (i2 : ℝ) * δ < ((i1 : ℝ) + 1) * δ := lt_of_le_of_lt hx'.1.1 hx.1.2
    nlinarith
  have h_j1_lt : (j1 : ℝ) < (j2 : ℝ) + 1 := by
    have h : (j1 : ℝ) * δ < ((j2 : ℝ) + 1) * δ := lt_of_le_of_lt hx.2.1 hx'.2.2
    nlinarith
  have h_j2_lt : (j2 : ℝ) < (j1 : ℝ) + 1 := by
    have h : (j2 : ℝ) * δ < ((j1 : ℝ) + 1) * δ := lt_of_le_of_lt hx'.2.1 hx.2.2
    nlinarith
  have h_i1_int : i1 < i2 + 1 := by exact_mod_cast h_i1_lt
  have h_i2_int : i2 < i1 + 1 := by exact_mod_cast h_i2_lt
  have h_j1_int : j1 < j2 + 1 := by exact_mod_cast h_j1_lt
  have h_j2_int : j2 < j1 + 1 := by exact_mod_cast h_j2_lt
  exact ⟨by omega, by omega⟩

lemma dyadicSquare_eq_or_disjoint' {δ : ℝ} (hδ : 0 < δ) {i1 j1 i2 j2 : ℤ} :
    (dyadicSquare δ i1 j1 = dyadicSquare δ i2 j2) ∨
    Disjoint (dyadicSquare δ i1 j1) (dyadicSquare δ i2 j2) := by
  by_cases h : i1 = i2 ∧ j1 = j2
  · rcases h with ⟨rfl, rfl⟩; exact Or.inl rfl
  · have h' : i1 ≠ i2 ∨ j1 ≠ j2 := by tauto
    refine Or.inr (Set.disjoint_left.mpr fun x h1 h2 => ?_)
    rcases h' with (h_i | h_j)
    · have h5 : (i1 : ℝ) * δ ≤ x 0 := h1.1.1
      have h6 : x 0 < ((i1 : ℝ) + 1) * δ := h1.1.2
      have h7 : (i2 : ℝ) * δ ≤ x 0 := h2.1.1
      have h8 : x 0 < ((i2 : ℝ) + 1) * δ := h2.1.2
      have h9 : (i1 : ℝ) < (i2 : ℝ) + 1 := by nlinarith
      have h10 : (i2 : ℝ) < (i1 : ℝ) + 1 := by nlinarith
      have h11 : i1 < i2 + 1 := by exact_mod_cast h9
      have h12 : i2 < i1 + 1 := by exact_mod_cast h10
      have h13 : i1 = i2 := by omega
      exact h_i h13
    · have h5 : (j1 : ℝ) * δ ≤ x 1 := h1.2.1
      have h6 : x 1 < ((j1 : ℝ) + 1) * δ := h1.2.2
      have h7 : (j2 : ℝ) * δ ≤ x 1 := h2.2.1
      have h8 : x 1 < ((j2 : ℝ) + 1) * δ := h2.2.2
      have h9 : (j1 : ℝ) < (j2 : ℝ) + 1 := by nlinarith
      have h10 : (j2 : ℝ) < (j1 : ℝ) + 1 := by nlinarith
      have h11 : j1 < j2 + 1 := by exact_mod_cast h9
      have h12 : j2 < j1 + 1 := by exact_mod_cast h10
      have h13 : j1 = j2 := by omega
      exact h_j h13

/-! # Intersection implies parentBy match -/

lemma parentBy_of_intersection {m k : ℕ} (hk : k ≤ m) {c d a b : ℤ}
    (h_inter : (dyadicSquare ((1 / 2 : ℝ) ^ m) c d ∩
      dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) a b).Nonempty) :
    parentBy k (c, d) = (a, b) := by
  let coarse_idx := parentBy k (c, d)
  have h_arith : m - k + k = m := by omega
  have h_contain : dyadicSquare ((1 / 2 : ℝ) ^ m) c d ⊆
      dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) coarse_idx.1 coarse_idx.2 := by
    have h := parentBy_square_containment (m := m - k) (k := k) c d coarse_idx.1 coarse_idx.2 rfl
    rw [h_arith] at h
    exact h
  rcases h_inter with ⟨x, hx_fine, hx_coarse⟩
  have h_in_parent : x ∈ dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) coarse_idx.1 coarse_idx.2 :=
    h_contain hx_fine
  by_cases h_eq : coarse_idx = (a, b)
  · exact h_eq
  · have h_sq_ne : dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) coarse_idx.1 coarse_idx.2 ≠
        dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) a b := by
      intro h
      have h_inj := dyadicSquare_inj (by positivity) h
      have h_inj' : coarse_idx = (a, b) := by
        exact Prod.ext h_inj.1 h_inj.2
      exact h_eq h_inj'
    have h_disj := (dyadicSquare_eq_or_disjoint' (by positivity)).resolve_left h_sq_ne
    have h_not_in : x ∉ dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) a b :=
      Set.disjoint_left.mp h_disj h_in_parent
    exfalso
    exact h_not_in hx_coarse

/-! # Intersection with coarse square -/

lemma setFromIndices_intersect_coarse {m k : ℕ} (hk : k ≤ m)
    (S : Finset (ℤ × ℤ)) (a b : ℤ) :
    setFromIndicesMD ((1 / 2 : ℝ) ^ m) S ∩
      dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) a b =
    setFromIndicesMD ((1 / 2 : ℝ) ^ m)
      (S.filter (fun idx => parentBy k idx = (a, b))) := by
  ext x
  simp only [setFromIndicesMD, Set.mem_inter_iff, Set.mem_iUnion₂,
    Finset.mem_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨idx, hidx, hx_fine⟩, hx_coarse⟩
    have h_parent : parentBy k idx = (a, b) :=
      parentBy_of_intersection hk ⟨x, hx_fine, hx_coarse⟩
    exact ⟨idx, ⟨hidx, h_parent⟩, hx_fine⟩
  · rintro ⟨idx, ⟨hidx, h_parent⟩, hx_fine⟩
    have h_arith : m - k + k = m := by omega
    have h_contain : dyadicSquare ((1 / 2 : ℝ) ^ m) idx.1 idx.2 ⊆
        dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) a b := by
      have h := parentBy_square_containment (m := m - k) (k := k) idx.1 idx.2 a b h_parent
      rw [h_arith] at h
      exact h
    exact ⟨⟨idx, hidx, hx_fine⟩, h_contain hx_fine⟩

/-! # dyadicSquareCount at coarser scale -/

lemma dyadicSquareCount_coarser {m k : ℕ} (hk : k ≤ m)
    (S : Finset (ℤ × ℤ)) :
    dyadicSquareCount ((1 / 2 : ℝ) ^ (m - k))
      (setFromIndicesMD ((1 / 2 : ℝ) ^ m) S) =
    ↑(S.image (parentBy k)).card := by
  let S_img : Finset (ℤ × ℤ) := S.image (parentBy k)
  have h_set : {p : ℤ × ℤ |
      (setFromIndicesMD ((1 / 2 : ℝ) ^ m) S ∩
        dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) p.1 p.2).Nonempty} =
      (S_img : Set (ℤ × ℤ)) := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h with ⟨x, hx1, hx2⟩
      rcases Set.mem_iUnion₂.mp hx1 with ⟨idx, hidx, hx_fine⟩
      have h_parent : parentBy k idx = p := parentBy_of_intersection hk ⟨x, hx_fine, hx2⟩
      have h_in : p ∈ S_img := by
        rw [Finset.mem_image]
        exact ⟨idx, hidx, h_parent⟩
      exact h_in
    · intro h
      have h_in : p ∈ S_img := h
      rw [Finset.mem_image] at h_in
      rcases h_in with ⟨idx, hidx, h_parent⟩
      let coarse_idx := parentBy k idx
      have h_coarse_eq : coarse_idx = p := h_parent
      have h_arith : m - k + k = m := by omega
      have h_contain : dyadicSquare ((1 / 2 : ℝ) ^ m) idx.1 idx.2 ⊆
          dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) coarse_idx.1 coarse_idx.2 := by
        have h := parentBy_square_containment (m := m - k) (k := k) idx.1 idx.2 coarse_idx.1 coarse_idx.2 rfl
        rw [h_arith] at h
        exact h
      have hδ_pos : 0 < (1 / 2 : ℝ) ^ m := by positivity
      rcases dyadicSquare_nonempty hδ_pos idx.1 idx.2 with ⟨x, hx⟩
      have h_x_in_coarse : x ∈ dyadicSquare ((1 / 2 : ℝ) ^ (m - k)) p.1 p.2 := by
        rw [h_coarse_eq] at h_contain
        exact h_contain hx
      exact ⟨x, Set.mem_iUnion₂.mpr ⟨idx, hidx, hx⟩, h_x_in_coarse⟩
  rw [dyadicSquareCount, h_set]
  have h_encard : (S_img : Set (ℤ × ℤ)).encard = ↑S_img.card := by
    simp
  rw [h_encard]
  <;> rfl

/-! # Arithmetic helpers -/

lemma arith_q_add {m i q : ℕ} (hi : i + 1 ≤ m) :
    q + q * (m - (i + 1)) = q * (m - i) := by
  have h : m - i = m - (i + 1) + 1 := by omega
  rw [h] <;> ring

lemma arith_q_sub1 {m i q : ℕ} (hi : i ≤ m) :
    q * m - q * (m - i) = q * i := by
  have h2 : m = i + (m - i) := by omega
  have h5 : q * m = q * (i + (m - i)) := by
    exact congr_arg (fun x : ℕ => q * x) h2
  have h6 : q * (i + (m - i)) = q * i + q * (m - i) := by
    rw [Nat.mul_add]
  have h3 : q * m = q * i + q * (m - i) := by
    rw [h5, h6]
  rw [h3]
  <;> omega

lemma arith_q_sub2 {m i q : ℕ} (hi : i + 1 ≤ m) :
    q * m - q * (m - (i + 1)) = q * (i + 1) := by
  have h2 : m = (i + 1) + (m - (i + 1)) := by omega
  have h5 : q * m = q * ((i + 1) + (m - (i + 1))) := by
    exact congr_arg (fun x : ℕ => q * x) h2
  have h6 : q * ((i + 1) + (m - (i + 1))) = q * (i + 1) + q * (m - (i + 1)) := by
    rw [Nat.mul_add]
  have h3 : q * m = q * (i + 1) + q * (m - (i + 1)) := by
    rw [h5, h6]
  rw [h3]
  <;> omega

/-! # image-filter commutation (generalized for step q) -/

lemma image_filter_commute_q {m i q : ℕ} (hi : i + 1 ≤ m) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (a b : ℤ) :
    (S.filter (fun idx => parentBy (q * (m - i)) idx = (a, b))).image (parentBy (q * (m - (i + 1)))) =
    (S.image (parentBy (q * (m - (i + 1))))).filter (fun idx => parentBy q idx = (a, b)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨idx, ⟨hidx, h_parent⟩, rfl⟩
    have h_arith : q + q * (m - (i + 1)) = q * (m - i) := arith_q_add hi
    have h1 : parentBy q (parentBy (q * (m - (i + 1))) idx) = parentBy (q * (m - i)) idx := by
      rw [BasicUniformization.parentBy_comp q (q * (m - (i + 1))) idx, h_arith]
    exact ⟨⟨idx, hidx, rfl⟩, by rw [h1, h_parent]⟩
  · rintro ⟨⟨idx, hidx, rfl⟩, h_parent2⟩
    have h1 : parentBy (q * (m - i)) idx = (a, b) := by
      have h_arith : q * (m - i) = q + q * (m - (i + 1)) := (arith_q_add hi).symm
      have h2 : parentBy (q * (m - i)) idx = parentBy q (parentBy (q * (m - (i + 1))) idx) := by
        rw [h_arith]
        exact (BasicUniformization.parentBy_comp q (q * (m - (i + 1))) idx).symm
      rw [h2, h_parent2]
    exact ⟨idx, ⟨hidx, h1⟩, rfl⟩

/-! # Main bridge lemma (base Δ = (1/2)^q) -/

/-- Convert exact per-level branching counts from `multi_level_thin`
    (with index map a(j) = q*j) into `IsDyadicUniform` with base Δ = (1/2)^q. -/
lemma thin_output_to_IsDyadicUniform {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    (S' : Finset (ℤ × ℤ)) (hS'_nonempty : S'.Nonempty)
    (N : Fin m → ℕ) (hN_pos : ∀ j, 1 ≤ N j)
    (h_exact : ∀ (j : Fin m) (g : ℤ × ℤ),
      let fineSquares := S'.image (parentBy (q * (m - (j + 1))))
      let count := (fineSquares.filter (fun idx => parentBy q idx = g)).card
      count = 0 ∨ count = N j) :
    IsDyadicUniform (setFromIndicesMD ((1 / 2 : ℝ) ^ (q * m)) S') m ((1 / 2 : ℝ) ^ q)
      (fun i : ℕ => if h : i < m then N ⟨i, h⟩ else 1) := by
  let Δ := (1 / 2 : ℝ) ^ q
  let P := setFromIndicesMD (Δ ^ m) S'
  have hΔm : Δ ^ m = (1 / 2 : ℝ) ^ (q * m) := by
    rw [←pow_mul] <;> ring
  have h_qm_pos : 0 < q * m := mul_pos hq hm
  have hδ_pos : 0 < (1 / 2 : ℝ) ^ (q * m) := by positivity
  let P' := setFromIndicesMD ((1 / 2 : ℝ) ^ (q * m)) S'
  have hP_eq : P = P' := by
    dsimp only [P, P']
    rw [hΔm]
  have hP_nonempty' : P'.Nonempty := by
    rcases hS'_nonempty with ⟨idx, hidx⟩
    rcases dyadicSquare_nonempty hδ_pos idx.1 idx.2 with ⟨x, hx⟩
    have hx' : x ∈ dyadicSquare (Δ ^ m) idx.1 idx.2 := by
      rw [hΔm]; exact hx
    have h_x_in_P : x ∈ P := Set.mem_iUnion₂.mpr ⟨idx, hidx, hx'⟩
    rw [hP_eq] at h_x_in_P
    exact ⟨x, h_x_in_P⟩
  let N' : ℕ → ℕ := fun i => if h : i < m then N ⟨i, h⟩ else 1
  have h_main : ∀ (i : ℕ), i < m → ∀ (a b : ℤ),
      (P' ∩ dyadicSquare (Δ ^ i) a b).Nonempty →
      (dyadicSquareCount (Δ ^ (i + 1)) (P' ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) =
      (↑(N' i) : ENNReal) := by
    intro i hi a b h_nonempty
    have hN_i : N' i = N ⟨i, hi⟩ := by
      simp [N', hi]
    have hΔi : Δ ^ i = (1 / 2 : ℝ) ^ (q * i) := by rw [←pow_mul] <;> ring
    have hΔi1 : Δ ^ (i + 1) = (1 / 2 : ℝ) ^ (q * (i + 1)) := by rw [←pow_mul] <;> ring
    have h_arith1 : q * m - q * (m - i) = q * i := arith_q_sub1 (by omega)
    have h_arith2 : q * m - q * (m - (i + 1)) = q * (i + 1) := arith_q_sub2 (by omega)
    have h_k1_le : q * (m - i) ≤ q * m := by
      have h : m - i ≤ m := by omega
      exact Nat.mul_le_mul_left q h
    have h_k2_le : q * (m - (i + 1)) ≤ q * m := by
      have h : m - (i + 1) ≤ m := by omega
      exact Nat.mul_le_mul_left q h
    let j : Fin m := ⟨i, hi⟩
    let g : ℤ × ℤ := (a, b)
    let fineSquares := S'.image (parentBy (q * (m - (i + 1))))
    let count := (fineSquares.filter (fun idx => parentBy q idx = g)).card
    have h_count_range : count = 0 ∨ count = N j := h_exact j g
    have h_count_pos : 0 < count := by
      rcases h_nonempty with ⟨x, hxP, hx_coarse⟩
      rcases Set.mem_iUnion₂.mp hxP with ⟨idx, hidx, hx_fine⟩
      have hx_fine' : x ∈ dyadicSquare ((1 / 2 : ℝ) ^ (q * m)) idx.1 idx.2 := hx_fine
      have h_coarse_scale : Δ ^ i = (1 / 2 : ℝ) ^ (q * m - q * (m - i)) := by
        rw [hΔi, ←h_arith1]
      have hx_coarse' : x ∈ dyadicSquare ((1 / 2 : ℝ) ^ (q * m - q * (m - i))) a b := by
        rw [←h_coarse_scale]
        exact hx_coarse
      have h_parent : parentBy (q * (m - i)) idx = (a, b) :=
        parentBy_of_intersection h_k1_le ⟨x, hx_fine', hx_coarse'⟩
      let q_idx := parentBy (q * (m - (i + 1))) idx
      have hq_in : q_idx ∈ fineSquares := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
      have hq_parent : parentBy q q_idx = (a, b) := by
        have h1 : parentBy q q_idx = parentBy (q * (m - i)) idx := by
          have h_arith : q + q * (m - (i + 1)) = q * (m - i) := arith_q_add (by omega)
          rw [BasicUniformization.parentBy_comp q (q * (m - (i + 1))) idx, h_arith]
        rw [h1, h_parent]
      have h_in_filter : q_idx ∈ fineSquares.filter (fun idx => parentBy q idx = g) := by
        simp only [Finset.mem_filter]; exact ⟨hq_in, hq_parent⟩
      exact Finset.card_pos.mpr ⟨q_idx, h_in_filter⟩
    have h_count_eq : count = N j := by
      rcases h_count_range with (h0 | h_eq)
      · exfalso; rw [h0] at h_count_pos; simpa using h_count_pos
      · exact h_eq
    have h_intersect_eq : P' ∩ dyadicSquare (Δ ^ i) a b =
        setFromIndicesMD ((1 / 2 : ℝ) ^ (q * m))
          (S'.filter (fun idx => parentBy (q * (m - i)) idx = (a, b))) := by
      rw [hΔi]
      have h_lemma := setFromIndices_intersect_coarse h_k1_le S' a b
      have h_pow_eq : (1 / 2 : ℝ) ^ (q * m - q * (m - i)) = (1 / 2 : ℝ) ^ (q * i) := by rw [h_arith1]
      rw [h_pow_eq] at h_lemma
      exact h_lemma
    have h_count_set : dyadicSquareCount ((1 / 2 : ℝ) ^ (q * (i + 1)))
        (setFromIndicesMD ((1 / 2 : ℝ) ^ (q * m))
          (S'.filter (fun idx => parentBy (q * (m - i)) idx = (a, b)))) =
        ↑((S'.filter (fun idx => parentBy (q * (m - i)) idx = (a, b))).image
          (parentBy (q * (m - (i + 1))))).card := by
      have h_pow_eq : (1 / 2 : ℝ) ^ (q * (i + 1)) = (1 / 2 : ℝ) ^ (q * m - q * (m - (i + 1))) := by
        rw [h_arith2]
      rw [h_pow_eq]
      exact dyadicSquareCount_coarser h_k2_le _
    have hi_succ : i + 1 ≤ m := by omega
    have h_comm := image_filter_commute_q hi_succ hq S' a b
    have h_enat : dyadicSquareCount (Δ ^ (i + 1)) (P' ∩ dyadicSquare (Δ ^ i) a b) = ↑(N' i) := by
      rw [h_intersect_eq, hΔi1, h_count_set, h_comm]
      have h_card : ((S'.image (parentBy (q * (m - (i + 1))))).filter (fun idx => parentBy q idx = (a, b))).card = count := by
        congr <;> rfl
      rw [h_card, h_count_eq, hN_i] <;> rfl
    exact_mod_cast h_enat
  have hΔ_pos : 0 < Δ := by positivity
  have hΔ_lt_one : Δ < 1 := by
    have hq' : 1 ≤ q := by linarith
    have h₁ : (1 / 2 : ℝ) ^ q ≤ (1 / 2 : ℝ) ^ 1 := by
      have h_base : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have h_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
      exact pow_le_pow_of_le_one h_base h_le_one hq'
    have h₂ : (1 / 2 : ℝ) ^ 1 = 1 / 2 := by norm_num
    rw [h₂] at h₁
    have h₃ : (1 / 2 : ℝ) ^ q < 1 := by linarith
    exact h₃
  have hN'_pos : ∀ i < m, N' i ≥ 1 := by
    intro i hi
    have h_simp : N' i = N ⟨i, hi⟩ := by simp [N', hi]
    rw [h_simp]
    exact hN_pos ⟨i, hi⟩
  exact ⟨hΔ_pos, hΔ_lt_one, hP_nonempty', hN'_pos, h_main⟩

end DiscretisedFurstenbergEstimate.Section9Bridge
