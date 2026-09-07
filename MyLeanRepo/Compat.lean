module

/-
# Compatibility layer for reference code

Provides aliases mapping reference names (ProductLikeIncidence.*) to the
target file's definitions, plus extra definitions and infrastructure lemmas
needed by copied reference modules.

## Aliases

- `productLikeRealLineCopy := realLineCopy`
- `projectionSet := affineProjection`
- `projectionSet1D := affineProjection1D`
- `IsProductLikeRealDeltaSCSet := IsRealDeltaSet`

## Extra definitions

- `productLikeIntegerGrid`, `productLikeUnitGrid`, `deltaGrid`
- `cellRealization`, `realCubeIndexSet`

## Infrastructure lemmas

- Dyadic: `dyadicScales_pos`, `dyadicCube_nonempty`, `dyadicCoveringNumber_mono`, `dyadicCubesMeeting_finite`
- Real line: `realLineCopy_bounded`, `realCoveringNumber_eq_card`
- Projection: `projectionSet.monotone`, `projectionSet.bounded`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal

namespace ProductLikeIncidence

/-! ### Aliases to target definitions -/
-- `productLikeRealLineCopy`, `IsProductLikeRealDeltaSCSet` are provided by CoreDefinitions.

abbrev productLikeRealLineCopy (A : Set ℝ) : Set (EuclideanSpace ℝ (Fin 1)) :=
  _root_.productLikeRealLineCopy A

abbrev projectionSet (y : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  affineProjection y P

abbrev projectionSet1D (y : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 1)) :=
  affineProjection1D y P

/-! ### Extra definitions -/

/-- Alias for `productLikeIntegerGrid` (provided by CoreDefinitions). -/
def deltaGrid (δ : ℝ) : Set ℝ := productLikeIntegerGrid δ

/-- The union of cells indexed by a set `S`. -/
def cellRealization {α : Type*}
    (cell : α → Set (EuclideanSpace ℝ (Fin 2))) (S : Set α) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ a ∈ S, cell a

/-- The set of integer indices of δ-dyadic intervals meeting a real set S. -/
def realCubeIndexSet (δ : ℝ) (S : Set ℝ) : Set ℤ :=
  {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}

/-- Equivalence between the `Ico`-based definition and the existential form. -/
lemma realCubeIndexSet_mem_iff {δ : ℝ} {S : Set ℝ} {k : ℤ} :
    k ∈ realCubeIndexSet δ S ↔
      ∃ (x : ℝ), x ∈ S ∧ δ * (k : ℝ) ≤ x ∧ x < δ * ((k : ℝ) + 1) := by
  simp only [realCubeIndexSet, Set.mem_setOf_eq, Set.Nonempty]
  constructor
  · rintro ⟨x, hxIco, hxS⟩
    exact ⟨x, hxS, hxIco.1, hxIco.2⟩
  · rintro ⟨x, hxS, h1, h2⟩
    exact ⟨x, ⟨h1, h2⟩, hxS⟩

/-! ### Dyadic scale properties -/

/-! ### Dyadic cube properties -/


/-! ### Grid properties -/


/-! ### Real line copy properties -/

lemma realCubeIndexSet_finite {δ : ℝ} {S : Set ℝ} (hδ : 0 < δ)
    (hS : Bornology.IsBounded S) : (realCubeIndexSet δ S).Finite := by
  have h1 : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ S, |x| ≤ C := by
    have h2 : ∃ (C : ℝ), ∀ x ∈ S, ‖x‖ ≤ C := isBounded_iff_forall_norm_le.mp hS
    rcases h2 with ⟨C, hC⟩
    let C' := max C 0
    have hC'_nonneg : 0 ≤ C' := by positivity
    have hC'_bound : ∀ x ∈ S, |x| ≤ C' := by
      intro x hx
      have h3 : ‖x‖ ≤ C := hC x hx
      have h4 : |x| ≤ C := by simpa [Real.norm_eq_abs] using h3
      have h5 : C ≤ C' := le_max_left C 0
      linarith
    exact ⟨C', hC'_nonneg, hC'_bound⟩
  rcases h1 with ⟨C, hC_nonneg, hC⟩
  let lo : ℤ := ⌊-C / δ - 1⌋
  let hi : ℤ := ⌈C / δ + 1⌉
  have h_sub : realCubeIndexSet δ S ⊆ Set.Icc lo hi := by
    intro k hk
    rcases hk with ⟨x, ⟨h_lower, h_upper⟩, hxS⟩
    have h_abs : |x| ≤ C := hC x hxS
    have h1 : -C ≤ x := (abs_le.mp h_abs).1
    have h2 : x ≤ C := (abs_le.mp h_abs).2
    have h3 : (lo : ℝ) ≤ (k : ℝ) := by
      have h4 : (lo : ℝ) ≤ -C / δ - 1 := Int.floor_le (-C / δ - 1)
      have h5 : -C / δ - 1 < (k : ℝ) := by
        have h6 : -C < δ * ((k : ℝ) + 1) := by linarith
        have h7 : (-C : ℝ) / δ < (δ * ((k : ℝ) + 1)) / δ := by gcongr
        have h8 : (δ * ((k : ℝ) + 1)) / δ = (k : ℝ) + 1 := by
          field_simp [hδ.ne'] <;> ring
        rw [h8] at h7; linarith
      linarith
    have h4 : (k : ℝ) ≤ (hi : ℝ) := by
      have h5 : C / δ + 1 ≤ (hi : ℝ) := Int.le_ceil (C / δ + 1)
      have h6 : (k : ℝ) ≤ C / δ := by
        have h7 : δ * (k : ℝ) ≤ C := by linarith
        have h8 : (δ * (k : ℝ)) / δ ≤ C / δ := by gcongr
        have h9 : (δ * (k : ℝ)) / δ = (k : ℝ) := by
          field_simp [hδ.ne'] <;> ring
        rw [h9] at h8; exact h8
      linarith
    exact ⟨Int.cast_le.mp h3, Int.cast_le.mp h4⟩
  exact Set.Finite.subset (Set.finite_Icc lo hi) h_sub

/-- The dyadic covering number of a real-line copy equals the encard of
    its cube index set. -/
lemma realCoveringNumber_eq_card {δ : ℝ} {S : Set ℝ}
    (hδ : 0 < δ) (hS_bdd : Bornology.IsBounded S) :
    dyadicCoveringNumber δ (productLikeRealLineCopy S) =
      (realCubeIndexSet δ S).encard := by
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k =>
    dyadicCube δ (fun (_ : Fin 1) => k)
  have h_main : dyadicCubesMeeting δ (productLikeRealLineCopy S) =
      f '' (realCubeIndexSet δ S) := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image, realCubeIndexSet]
    constructor
    · rintro ⟨hQ_cube, ⟨p, hpQ, hpS⟩⟩
      rcases hQ_cube with ⟨j, hj⟩
      have hpQ' : p ∈ dyadicCube δ j := by
        rw [←hj]; exact hpQ
      have h_j0 : j 0 ∈ (realCubeIndexSet δ S) := by
        have h1 : p 0 ∈ Set.Ico (δ * (j 0 : ℝ)) (δ * ((j 0 : ℝ) + 1)) := hpQ' 0
        exact ⟨p 0, ⟨h1, hpS⟩⟩
      have h_eq : Q = f (j 0) := by
        have h_j : j = fun (_ : Fin 1) => j 0 := by
          funext i
          have h_i0 : i = 0 := by exact Fin.eq_zero i
          rw [h_i0]
        rw [hj, h_j] <;> rfl
      exact ⟨j 0, h_j0, h_eq.symm⟩
    · rintro ⟨k, hk, rfl⟩
      rcases hk with ⟨x, hx⟩
      have hIco : x ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hx.1
      have hxS : x ∈ S := hx.2
      have h_lower : δ * (k : ℝ) ≤ x := hIco.1
      have h_upper : x < δ * ((k : ℝ) + 1) := hIco.2
      let j : Fin 1 → ℤ := fun _ => k
      have hQ_cube : f k ∈ dyadicCubes 1 δ := by
        simp only [f]
        exact ⟨j, rfl⟩
      let g : Fin 1 → ℝ := fun _ => x
      let e : EuclideanSpace ℝ (Fin 1) ≃ (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ
      let p : EuclideanSpace ℝ (Fin 1) := e.symm g
      have hpQ : p ∈ f k := by
        intro i
        have h_i0 : i = 0 := by exact Fin.eq_zero i
        rw [h_i0]
        exact ⟨h_lower, h_upper⟩
      have hpS : p ∈ productLikeRealLineCopy S := by
        simp only [productLikeRealLineCopy, p, g, Set.mem_setOf_eq]
        exact hxS
      exact ⟨hQ_cube, ⟨p, hpQ, hpS⟩⟩
  rw [dyadicCoveringNumber, h_main]
  have h_cube_inj : Function.Injective (dyadicCube δ : (Fin 1 → ℤ) → Set (EuclideanSpace ℝ (Fin 1))) := by
    intro k k' h
    have h_nonempty : (dyadicCube δ k).Nonempty := dyadicCube_nonempty hδ k
    rcases h_nonempty with ⟨x, hx⟩
    have hx' : x ∈ dyadicCube δ k' := by rw [h] at hx; exact hx
    have h11 : δ * (k 0 : ℝ) ≤ x 0 := (hx 0).1
    have h12 : x 0 < δ * ((k 0 : ℝ) + 1) := (hx 0).2
    have h21 : δ * (k' 0 : ℝ) ≤ x 0 := (hx' 0).1
    have h22 : x 0 < δ * ((k' 0 : ℝ) + 1) := (hx' 0).2
    have h3 : (k 0 : ℝ) < (k' 0 : ℝ) + 1 := by nlinarith
    have h4 : (k' 0 : ℝ) < (k 0 : ℝ) + 1 := by nlinarith
    have h3' : k 0 < k' 0 + 1 := by exact_mod_cast h3
    have h4' : k' 0 < k 0 + 1 := by exact_mod_cast h4
    have h5 : k 0 = k' 0 := by omega
    have h6 : k = k' := by
      funext i
      have h_i0 : i = 0 := Fin.eq_zero i
      rw [h_i0]
      exact h5
    exact h6
  have h_inj : Function.Injective f := by
    intro k1 k2 h
    have h' : (fun (_ : Fin 1) => k1) = (fun (_ : Fin 1) => k2) := h_cube_inj h
    have h_eq : k1 = k2 := by
      have h9 := congr_fun h' 0
      simpa using h9
    exact h_eq
  have h_inj_on : Set.InjOn f (realCubeIndexSet δ S) := fun x _ y _ h => h_inj h
  exact Set.InjOn.encard_image h_inj_on

/-! ### IsDeltaSCSet monotonicity -/

lemma realCoveringNumber_eq_card_ennreal {δ : ℝ} {S : Set ℝ}
    (hδ : 0 < δ) (hS_bdd : Bornology.IsBounded S) :
    ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy S)) =
      ((realCubeIndexSet δ S).encard : ENNReal) := by
  have h_eq := realCoveringNumber_eq_card hδ hS_bdd
  rw [h_eq] <;> rfl

/-! ### Projection properties (in projectionSet namespace) -/

namespace projectionSet

/-- The projection is monotone in the input set. -/
lemma monotone (y : ℝ) {P₁ P₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (h : P₁ ⊆ P₂) :
    projectionSet y P₁ ⊆ projectionSet y P₂ := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  exact ⟨p, h hp, rfl⟩

/-- The 1D copy is monotone in the input set. -/
lemma monotone1D (y : ℝ) {P₁ P₂ : Set (EuclideanSpace ℝ (Fin 2))}
    (h : P₁ ⊆ P₂) :
    projectionSet1D y P₁ ⊆ projectionSet1D y P₂ := by
  intro x hx
  have h1 : x 0 ∈ projectionSet y P₁ := hx
  have h2 : x 0 ∈ projectionSet y P₂ := monotone y h h1
  exact h2

/-- `projectionSet y P` is the image of `P` under the linear functional. -/
lemma image_eq (y : ℝ) (P : Set (EuclideanSpace ℝ (Fin 2))) :
    projectionSet y P = (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) '' P :=
  rfl

/-- If `P` is bounded, then `projectionSet y P` is bounded. -/
lemma bounded (y : ℝ) {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : Bornology.IsBounded P) :
    Bornology.IsBounded (projectionSet y P) := by
  let f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    { toFun := fun p => p 0 * y + p 1
      map_add' := by
        intro p q
        simp [Pi.add_apply] <;> ring
      map_smul' := by
        intro c p
        simp [Pi.smul_apply] <;> ring }
  have h : Bornology.IsBounded (f '' P) :=
    Bornology.IsBounded.image f hP
  exact h

end projectionSet

end ProductLikeIncidence

end
