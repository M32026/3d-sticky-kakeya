module

/-
# Cube index set infrastructure

Extracted from DiscretizedPluennecke.lean:
- `realCubeIndexSet`: set of δ-dyadic cube indices meeting a real set
- `realCubeIndexSet_finite`: finiteness for bounded sets
- `mkPoint1`: construct 1D Euclidean point from real
- `realCoveringNumber_eq_card`: covering number equals index set cardinality
-/

public import MyLeanRepo.Infrastructure
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal

namespace bourgain_projection_theorem

/-- The set of δ-dyadic cube indices (in ℤ) whose half-open intervals
`[δ·k, δ·(k+1))` meet the real set `S`. -/
def realCubeIndexSet (δ : ℝ) (S : Set ℝ) : Set ℤ :=
  {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}

/-- For bounded `S`, the cube index set is finite. -/
lemma realCubeIndexSet_finite {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) : (realCubeIndexSet δ S).Finite := by
  have hB : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ S, |x| ≤ C := by
    have h1 : ∃ (C : ℝ), ∀ x ∈ S, ‖x‖ ≤ C := isBounded_iff_forall_norm_le.mp hS
    rcases h1 with ⟨C, hC⟩
    refine ⟨max C 0, by positivity, fun x hx => ?_⟩
    have h2 : ‖x‖ ≤ C := hC x hx
    have h3 : |x| ≤ C := by simpa [Real.norm_eq_abs] using h2
    exact h3.trans (le_max_left C 0)
  rcases hB with ⟨C, hC_nonneg, hC⟩
  have h1 : ∀ k ∈ realCubeIndexSet δ S, (k : ℝ) ≤ C / δ + 1 := by
    intro k hk
    rcases hk with ⟨x, ⟨hx1, _⟩, hxS⟩
    have h2 : |x| ≤ C := hC x hxS
    have h3 : x ≤ C := (abs_le.mp h2).2
    have h4 : δ * (k : ℝ) ≤ x := hx1
    have h5 : δ * (k : ℝ) ≤ C := by linarith
    have h6 : (k : ℝ) ≤ C / δ := by
      calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ C / δ := by
          apply div_le_div_of_nonneg_right h5
          positivity
    linarith
  have h2 : ∀ k ∈ realCubeIndexSet δ S, -(C / δ + 1) ≤ (k : ℝ) := by
    intro k hk
    rcases hk with ⟨x, ⟨_, hx2⟩, hxS⟩
    have h3 : |x| ≤ C := hC x hxS
    have h4 : -C ≤ x := (abs_le.mp h3).1
    have h5 : x < δ * ((k : ℝ) + 1) := hx2
    have h6 : -C < δ * ((k : ℝ) + 1) := by linarith
    have h7 : -(C / δ) < (k : ℝ) + 1 := by
      have h8 : (-C) / δ < (δ * ((k : ℝ) + 1)) / δ := by
        apply div_lt_div_of_pos_right h6 hδ
      have h_simp : (δ * ((k : ℝ) + 1)) / δ = (k : ℝ) + 1 := by
        field_simp [hδ.ne'] <;> ring
      rw [h_simp] at h8
      have h9 : (-C) / δ = -(C / δ) := by ring
      rw [h9] at h8
      exact h8
    have h10 : -(C / δ + 1) < (k : ℝ) := by linarith
    exact h10.le
  let N_hi : ℤ := Int.ceil (C / δ + 1)
  let N_lo : ℤ := Int.floor (-(C / δ + 1))
  have h3 : realCubeIndexSet δ S ⊆ Set.Icc N_lo N_hi := by
    intro k hk
    have h4 : (k : ℝ) ≤ C / δ + 1 := h1 k hk
    have h5 : -(C / δ + 1) ≤ (k : ℝ) := h2 k hk
    have h6 : k ≤ N_hi := by
      have h7 : (k : ℝ) ≤ C / δ + 1 := h4
      have h8 : (k : ℝ) ≤ (N_hi : ℝ) := by
        exact le_trans h7 (Int.le_ceil (C / δ + 1))
      exact_mod_cast h8
    have h7 : N_lo ≤ k := by
      have h8 : (N_lo : ℝ) ≤ -(C / δ + 1) := Int.floor_le (-(C / δ + 1))
      have h9 : (N_lo : ℝ) ≤ (k : ℝ) := by linarith
      exact_mod_cast h9
    exact ⟨h7, h6⟩
  exact Set.Finite.subset (Set.finite_Icc _ _) h3

/-- Helper: construct a 1D Euclidean point from a real number. -/
def mkPoint1 (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun (_ : Fin 1) => x)

/-- The dyadic covering number equals the cardinality of the cube index set. -/
lemma realCoveringNumber_eq_card {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) :
    ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy S)) =
      ENat.toENNReal (realCubeIndexSet δ S).encard := by
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) :=
    fun k => dyadicCube δ (fun (_ : Fin 1) => k)
  have h_inj : Set.InjOn f (realCubeIndexSet δ S) := by
    intro k1 _ k2 _ h
    have h' : f k1 = f k2 := h
    let p : EuclideanSpace ℝ (Fin 1) := mkPoint1 (δ * (k1 : ℝ))
    have hp_val : p 0 = δ * (k1 : ℝ) := by rfl
    have hp1 : p ∈ f k1 := by
      have h1 : ∀ (i : Fin 1), p i ∈ Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) := by
        intro i; fin_cases i <;> simp [hp_val] <;> linarith
      exact h1
    rw [h'] at hp1
    have h5 : ∀ (i : Fin 1), p i ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := hp1
    have h6 := h5 0
    have h7 : δ * (k2 : ℝ) ≤ p 0 := h6.1
    have h8 : p 0 < δ * ((k2 : ℝ) + 1) := h6.2
    rw [hp_val] at h7 h8
    have h9 : (k2 : ℝ) ≤ (k1 : ℝ) := by
      have h91 : δ * (k2 : ℝ) ≤ δ * (k1 : ℝ) := h7
      have h92 : (δ * (k2 : ℝ)) / δ ≤ (δ * (k1 : ℝ)) / δ := by gcongr
      have h93 : (δ * (k2 : ℝ)) / δ = (k2 : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h94 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ.ne'] <;> ring
      rw [h93, h94] at h92
      exact h92
    have h10 : (k1 : ℝ) < (k2 : ℝ) + 1 := by
      have h101 : δ * (k1 : ℝ) < δ * ((k2 : ℝ) + 1) := h8
      have h102 : (δ * (k1 : ℝ)) / δ < (δ * ((k2 : ℝ) + 1)) / δ := by gcongr
      have h103 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h104 : (δ * ((k2 : ℝ) + 1)) / δ = (k2 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      rw [h103, h104] at h102
      exact h102
    have h10' : k1 < k2 + 1 := by exact_mod_cast h10
    have h11 : k1 ≤ k2 := by linarith
    have h12 : k2 ≤ k1 := by exact_mod_cast h9
    exact le_antisymm h11 h12
  have h_main : dyadicCubesMeeting (d := 1) δ (productLikeRealLineCopy S) =
      f '' (realCubeIndexSet δ S) := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hQ, ⟨x, hxQ, hxS⟩⟩
      rcases hQ with ⟨k, rfl⟩
      let k0 : ℤ := k 0
      have hk : k0 ∈ realCubeIndexSet δ S := by
        simp only [realCubeIndexSet, Set.mem_setOf_eq]
        have h1 : x 0 ∈ Set.Ico (δ * (k0 : ℝ)) (δ * ((k0 : ℝ) + 1)) := hxQ 0
        have h2 : x 0 ∈ S := by simpa [productLikeRealLineCopy, realLineCopy] using hxS
        exact ⟨x 0, h1, h2⟩
      have h_eq : dyadicCube δ k = f k0 := by
        funext y
        simp [f, dyadicCube]
        <;> aesop
      rw [h_eq]
      exact ⟨k0, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hQ : f k ∈ dyadicCubes 1 δ := by
        simp [f, dyadicCubes] <;> exact ⟨(fun _ => k), rfl⟩
      have h_nonempty : ((f k) ∩ productLikeRealLineCopy S).Nonempty := by
        simp only [realCubeIndexSet, Set.mem_setOf_eq] at hk
        rcases hk with ⟨x, ⟨hx1, hx2⟩, hxS⟩
        let p : EuclideanSpace ℝ (Fin 1) := mkPoint1 x
        have hp_val : p 0 = x := by rfl
        refine ⟨p, ?_⟩
        constructor
        · have h1 : ∀ (i : Fin 1), p i ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
            intro i; fin_cases i <;> simp [hp_val] <;> exact ⟨hx1, hx2⟩
          exact h1
        · have h2 : p 0 ∈ S := by
            rw [hp_val] <;> exact hxS
          simpa [productLikeRealLineCopy, realLineCopy] using h2
      exact ⟨hQ, h_nonempty⟩
  have h_finite : (realCubeIndexSet δ S).Finite := realCubeIndexSet_finite hδ hS
  let sFinset := h_finite.toFinset
  have hs : (sFinset : Set ℤ) = realCubeIndexSet δ S :=
    Set.Finite.coe_toFinset h_finite
  rw [dyadicCoveringNumber, h_main]
  have h_image_eq : (f '' (realCubeIndexSet δ S)) = (sFinset.image f : Set _) := by
    have h1 : f '' (realCubeIndexSet δ S) = f '' (sFinset : Set ℤ) := by rw [hs]
    rw [h1]
    ext y
    simp [Set.mem_image, Finset.mem_image]
    <;> tauto
  rw [h_image_eq]
  have h_inj' : Set.InjOn f (sFinset : Set ℤ) := by
    rw [hs]
    exact h_inj
  have h_card : (sFinset.image f).card = sFinset.card :=
    Finset.card_image_of_injOn h_inj'
  have h_encard1 : (sFinset.image f : Set (Set (EuclideanSpace ℝ (Fin 1)))).encard = (sFinset.image f).card :=
    Set.encard_coe_eq_coe_finsetCard (sFinset.image f)
  have h_encard2 : (realCubeIndexSet δ S).encard = sFinset.card :=
    Set.Finite.encard_eq_coe_toFinset_card h_finite
  rw [h_encard1, h_card, h_encard2]

end bourgain_projection_theorem
