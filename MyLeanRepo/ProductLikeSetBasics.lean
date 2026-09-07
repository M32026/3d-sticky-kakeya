module

/-
# Product-Like Set Basics

Basic properties of product-like incidence sets and their covering numbers.

## Main results

- `productLikeIncidenceSet_bounded`: boundedness from finite Y and bounded fibers
- `productLikeIncidenceSet_finite`: finiteness from finite Y and finite fibers
- `productLikeIncidenceSet_disjoint_fibers`: fibers are pairwise disjoint
- `productLikeIncidenceSet_encard`: cardinality equals sum of fiber cardinalities
- `grid_set_coveringNumber_eq_encard`: δ-covering number equals encard for grid sets
- `productLikeIncidenceSet_coveringNumber_eq_encard`: covering number = encard
- `IsProductLikeRealDeltaSCSet.min_size`: lower bound on size of a grid δ-set
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal

namespace ProductLikeIncidence

section Bounded

/-- If Y is finite and each fiber X_y is bounded, then the product-like set is bounded. -/
lemma productLikeIncidenceSet_bounded {Y : Set ℝ} {X : ℝ → Set ℝ}
    (hY : Y.Finite) (hX : ∀ y ∈ Y, Bornology.IsBounded (X y)) :
    Bornology.IsBounded (productLikeIncidenceSet Y X) := by
  let fiber (y : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
    {z | z 0 ∈ X y ∧ z 1 = y}
  let S : Set (Set (EuclideanSpace ℝ (Fin 2))) := fiber '' Y
  have hS_finite : S.Finite := hY.image _
  have h_main : ∀ (s : Set (EuclideanSpace ℝ (Fin 2))), s ∈ S → Bornology.IsBounded s := by
    intro s hs
    rcases hs with ⟨y, hy, rfl⟩
    have hXy : Bornology.IsBounded (X y) := hX y hy
    by_cases h_empty : X y = ∅
    · have h_fiber_empty : fiber y = ∅ := by
        ext z
        simp [fiber, h_empty]
      rw [h_fiber_empty]
      exact Bornology.isBounded_empty
    · rcases (Set.nonempty_iff_ne_empty.mpr h_empty) with ⟨x₀, hx₀⟩
      rcases Metric.isBounded_iff.mp hXy with ⟨C, hC⟩
      let c : EuclideanSpace ℝ (Fin 2) :=
        (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i => if i = 0 then x₀ else y
      have h_ball : fiber y ⊆ Metric.closedBall c C := by
        intro z hz
        have h1 : z 0 ∈ X y := hz.1
        have h2 : z 1 = y := hz.2
        have h3 : dist (z 0) x₀ ≤ C := hC h1 hx₀
        have h4 : |z 0 - x₀| ≤ C := by simpa [Real.dist_eq] using h3
        have h5 : dist z c = |z 0 - x₀| := by
          have h6 : dist z c = Real.sqrt ((z 0 - x₀) ^ 2 + (z 1 - y) ^ 2) := by
            simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two, c]
            <;> ring_nf
          rw [h6]
          have h7 : z 1 - y = 0 := by linarith [h2]
          rw [h7]
          have h8 : Real.sqrt ((z 0 - x₀) ^ 2 + (0 : ℝ) ^ 2) = |z 0 - x₀| := by
            have h9 : (z 0 - x₀) ^ 2 + (0 : ℝ) ^ 2 = (z 0 - x₀) ^ 2 := by ring
            rw [h9]
            have h10 : Real.sqrt ((z 0 - x₀) ^ 2) = |z 0 - x₀| := by
              rw [Real.sqrt_sq_eq_abs]
            exact h10
          exact h8
        simpa [Metric.mem_closedBall, h5] using h4
      have h_closedBall_bounded : Bornology.IsBounded (Metric.closedBall c C) :=
        Metric.isBounded_closedBall
      exact Bornology.IsBounded.subset h_closedBall_bounded h_ball
  have h_union : productLikeIncidenceSet Y X = ⋃₀ S := by
    ext z
    simp [S, fiber, productLikeIncidenceSet]
    <;> aesop
  rw [h_union]
  exact (Bornology.isBounded_sUnion hS_finite).mpr h_main

end Bounded

section Finite

/-- If Y is finite and each fiber X_y is finite, then the product-like set is finite. -/
lemma productLikeIncidenceSet_finite {Y : Set ℝ} {X : ℝ → Set ℝ}
    (hY : Y.Finite) (hX : ∀ y ∈ Y, (X y).Finite) :
    (productLikeIncidenceSet Y X).Finite := by
  have h_main : ∀ y ∈ Y, Set.Finite
      ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro y hy
    have hXy : (X y).Finite := hX y hy
    let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i => if i = 0 then x else y
    have h_eq : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} = f '' (X y) := by
      ext z
      simp only [f, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h
        refine ⟨z 0, h.1, ?_⟩
        ext i
        fin_cases i
        · simp
        · simpa using h.2.symm
      · rintro ⟨x, hx, rfl⟩
        simp [hx]
    rw [h_eq]
    exact hXy.image f
  exact Set.Finite.biUnion hY h_main

/-- Fibers for different y values are disjoint. -/
lemma productLikeIncidenceSet_disjoint_fibers {Y : Set ℝ} {X : ℝ → Set ℝ} :
    Set.PairwiseDisjoint Y (fun y =>
      {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y}) := by
  intro y _ y' _ hyy
  have h : Disjoint ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} : Set (EuclideanSpace ℝ (Fin 2)))
      ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y' ∧ z 1 = y'} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 : z 1 = y := hz.2
    have h2 : z 1 = y' := hz'.2
    exact hyy (h1.symm.trans h2)
  exact h

/-- The encard of the product-like set equals the finsum of fiber encards. -/
lemma productLikeIncidenceSet_encard {Y : Set ℝ} {X : ℝ → Set ℝ}
    (hY : Y.Finite) :
    (productLikeIncidenceSet Y X).encard =
      ∑ᶠ y ∈ Y, ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y}).encard := by
  exact Set.Finite.encard_biUnion hY productLikeIncidenceSet_disjoint_fibers

/-- Each fiber has an injection from X_y, so its encard equals (X y).encard. -/
lemma fiber_encard {X : ℝ → Set ℝ} {y : ℝ} :
    ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} : Set (EuclideanSpace ℝ (Fin 2))).encard
      = (X y).encard := by
  let f : ℝ → EuclideanSpace ℝ (Fin 2) := fun x =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm fun i => if i = 0 then x else y
  have h_eq : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} = f '' (X y) := by
    ext z
    simp only [f, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨z 0, h.1, ?_⟩
      ext i
      fin_cases i
      · simp
      · simpa using h.2.symm
    · rintro ⟨x, hx, rfl⟩
      simp [hx]
  rw [h_eq]
  have h_inj : Function.Injective f := by
    intro x x' h
    have h1 : (f x) 0 = (f x') 0 := by rw [h]
    simpa [f] using h1
  exact Function.Injective.encard_image h_inj (X y)

end Finite

section CoveringNumber

/-- Each point of the δ-grid lies in a unique δ-dyadic cube.
    Distinct grid points lie in distinct δ-cubes. -/
lemma grid_point_unique_cube {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x x' : EuclideanSpace ℝ (Fin d)}
    (hx : ∀ i, ∃ k : ℤ, x i = δ * (k : ℝ))
    (hx' : ∀ i, ∃ k : ℤ, x' i = δ * (k : ℝ))
    {k k' : Fin d → ℤ}
    (hxQ : x ∈ dyadicCube δ k) (hxQ' : x' ∈ dyadicCube δ k') :
    k = k' ↔ x = x' := by
  constructor
  · intro hk
    ext i
    rcases hx i with ⟨m, hm⟩
    rcases hx' i with ⟨m', hm'⟩
    have hki : x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hxQ i
    have hki' : x' i ∈ Set.Ico (δ * (k' i : ℝ)) (δ * ((k' i : ℝ) + 1)) := hxQ' i
    have h4 : m = k i := by
      have h51 : δ * (k i : ℝ) ≤ δ * (m : ℝ) := by
        rw [hm] at hki; exact hki.1
      have h52 : δ * (m : ℝ) < δ * ((k i : ℝ) + 1) := by
        rw [hm] at hki; exact hki.2
      have h53 : (k i : ℝ) ≤ (m : ℝ) := by nlinarith
      have h54 : (m : ℝ) < (k i : ℝ) + 1 := by nlinarith
      have h55 : k i ≤ m := by exact_mod_cast h53
      have h56 : m < k i + 1 := by exact_mod_cast h54
      omega
    have h5 : m' = k' i := by
      have h61 : δ * (k' i : ℝ) ≤ δ * (m' : ℝ) := by
        rw [hm'] at hki'; exact hki'.1
      have h62 : δ * (m' : ℝ) < δ * ((k' i : ℝ) + 1) := by
        rw [hm'] at hki'; exact hki'.2
      have h63 : (k' i : ℝ) ≤ (m' : ℝ) := by nlinarith
      have h64 : (m' : ℝ) < (k' i : ℝ) + 1 := by nlinarith
      have h65 : k' i ≤ m' := by exact_mod_cast h63
      have h66 : m' < k' i + 1 := by exact_mod_cast h64
      omega
    have h6 : k i = k' i := by rw [hk]
    rw [hm, hm', h4, h5, h6]
  · intro hxx'
    ext i
    rcases hx i with ⟨m, hm⟩
    have hki : x i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := hxQ i
    have hki' : x' i ∈ Set.Ico (δ * (k' i : ℝ)) (δ * ((k' i : ℝ) + 1)) := hxQ' i
    have h4 : m = k i := by
      have h51 : δ * (k i : ℝ) ≤ δ * (m : ℝ) := by
        rw [hm] at hki; exact hki.1
      have h52 : δ * (m : ℝ) < δ * ((k i : ℝ) + 1) := by
        rw [hm] at hki; exact hki.2
      have h53 : (k i : ℝ) ≤ (m : ℝ) := by nlinarith
      have h54 : (m : ℝ) < (k i : ℝ) + 1 := by nlinarith
      have h55 : k i ≤ m := by exact_mod_cast h53
      have h56 : m < k i + 1 := by exact_mod_cast h54
      omega
    have h_eq : x' i = x i := by rw [hxx']
    have h5 : m = k' i := by
      have h61 : δ * (k' i : ℝ) ≤ δ * (m : ℝ) := by
        rw [h_eq, hm] at hki'; exact hki'.1
      have h62 : δ * (m : ℝ) < δ * ((k' i : ℝ) + 1) := by
        rw [h_eq, hm] at hki'; exact hki'.2
      have h63 : (k' i : ℝ) ≤ (m : ℝ) := by nlinarith
      have h64 : (m : ℝ) < (k' i : ℝ) + 1 := by nlinarith
      have h65 : k' i ≤ m := by exact_mod_cast h63
      have h66 : m < k' i + 1 := by exact_mod_cast h64
      omega
    have h7 : k i = k' i := by
      rw [← h4, h5]
    exact_mod_cast h7

/-- For a set of grid points, the δ-covering number equals the encard. -/
lemma grid_set_coveringNumber_eq_encard {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin d))}
    (hA : ∀ x ∈ A, ∀ i : Fin d, ∃ k : ℤ, x i = δ * (k : ℝ)) :
    dyadicCoveringNumber δ A = A.encard := by
  by_cases hA_empty : A = ∅
  · rw [hA_empty]
    simp [dyadicCoveringNumber, dyadicCubesMeeting]
  · let k_fn (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A) : Fin d → ℤ :=
      fun i => Classical.choose (hA x hx i)
    have h_k_fn_spec : ∀ (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A) (i : Fin d),
        x i = δ * ((k_fn x hx i : ℝ)) := by
      intro x hx i
      exact Classical.choose_spec (hA x hx i)
    have h_in_cube : ∀ (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ A),
        x ∈ dyadicCube δ (k_fn x hx) := by
      intro x hx i
      have h := h_k_fn_spec x hx i
      exact ⟨by linarith [h], by linarith [h]⟩
    let f : A → Set (EuclideanSpace ℝ (Fin d)) := fun x =>
      dyadicCube δ (k_fn (x : EuclideanSpace ℝ (Fin d)) x.prop)
    have hf1 : ∀ (x : A), f x ∈ dyadicCubes d δ := by
      intro x
      exact ⟨_, rfl⟩
    have hf2 : ∀ (x : A), (x : EuclideanSpace ℝ (Fin d)) ∈ f x := by
      intro x
      exact h_in_cube (x : EuclideanSpace ℝ (Fin d)) x.prop
    have h_inj : Set.InjOn f (Set.univ : Set A) := by
      intro x _ y _ hxy
      have h1 : f x = f y := hxy
      have hx_in : (x : EuclideanSpace ℝ (Fin d)) ∈ f x := hf2 x
      have hy_in : (y : EuclideanSpace ℝ (Fin d)) ∈ f y := hf2 y
      rcases hf1 x with ⟨kx, hkx⟩
      have hx_in' : (x : EuclideanSpace ℝ (Fin d)) ∈ dyadicCube δ kx := by
        rw [← hkx]; exact hx_in
      have hy_in' : (y : EuclideanSpace ℝ (Fin d)) ∈ dyadicCube δ kx := by
        have h : (y : EuclideanSpace ℝ (Fin d)) ∈ f y := hy_in
        have h' : (y : EuclideanSpace ℝ (Fin d)) ∈ f x := h1.symm ▸ h
        exact hkx ▸ h'
      have h' : (x : EuclideanSpace ℝ (Fin d)) = (y : EuclideanSpace ℝ (Fin d)) :=
        (grid_point_unique_cube hδ (hA x x.prop) (hA y y.prop) hx_in' hy_in').mp rfl
      exact Subtype.ext h'
    have h_main1 : (f '' (Set.univ : Set A)) ⊆ dyadicCubesMeeting δ A := by
      intro Q hQ
      rcases hQ with ⟨x, _, rfl⟩
      exact ⟨hf1 x, ⟨x, hf2 x, x.prop⟩⟩
    have h_main2 : dyadicCubesMeeting δ A ⊆ (f '' (Set.univ : Set A)) := by
      intro Q hQ
      rcases hQ with ⟨hQ1, ⟨x, hxQ, hxA⟩⟩
      rcases hQ1 with ⟨k, hkQ⟩
      let x' : A := ⟨x, hxA⟩
      rcases hf1 x' with ⟨k', hk'⟩
      have h1 : x ∈ f x' := hf2 x'
      have h2 : x ∈ dyadicCube δ k := by
        have h21 : x ∈ Q := hxQ
        rw [hkQ] at h21
        exact h21
      have h_k_eq : k' = k := by
        have h3 : f x' = dyadicCube δ k' := hk'
        have h4 : x ∈ f x' := h1
        have h5 : x ∈ dyadicCube δ k' := by rw [h3] at h4; exact h4
        exact (grid_point_unique_cube hδ (hA x hxA) (hA x hxA) h5 h2).mpr rfl
      have h_cube_eq : f x' = Q := by
        rw [hk', h_k_eq, hkQ]
      exact ⟨x', Set.mem_univ x', h_cube_eq⟩
    have h_eq : dyadicCubesMeeting δ A = f '' (Set.univ : Set A) := by
      exact Set.Subset.antisymm h_main2 h_main1
    rw [dyadicCoveringNumber, h_eq]
    have h_inj' : Function.Injective f := by
      intro a b h
      exact h_inj (Set.mem_univ a) (Set.mem_univ b) h
    rw [Function.Injective.encard_image h_inj']
    simp

/-- For a product-like set on the δ-grid, the δ-covering number equals the encard. -/
lemma productLikeIncidenceSet_coveringNumber_eq_encard {δ : ℝ} (hδ : 0 < δ)
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    (hY : Y ⊆ productLikeUnitGrid δ)
    (hX : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ) :
    dyadicCoveringNumber δ (productLikeIncidenceSet Y X) =
      (productLikeIncidenceSet Y X).encard := by
  have h_grid : ∀ z ∈ productLikeIncidenceSet Y X, ∀ i : Fin 2, ∃ k : ℤ, z i = δ * (k : ℝ) := by
    intro z hz i
    rcases Set.mem_iUnion₂.mp hz with ⟨y, hy, hzy⟩
    have h_y1 : z 1 = y := hzy.2
    have h_y2 : y ∈ productLikeUnitGrid δ := hY hy
    have h_x1 : z 0 ∈ X y := hzy.1
    have h_x2 : z 0 ∈ productLikeUnitGrid δ := hX y hy h_x1
    fin_cases i
    · rcases h_x2.1 with ⟨k, hk⟩
      exact ⟨k, hk⟩
    · rcases h_y2.1 with ⟨k, hk⟩
      have h_goal : z 1 = δ * (k : ℝ) := by
        exact h_y1 ▸ hk
      exact ⟨k, h_goal⟩
  exact grid_set_coveringNumber_eq_encard hδ h_grid

/-- Lower bound: for each y ∈ Y, the δ-covering number is at least (X y).encard. -/
lemma productLikeIncidenceSet_coveringNumber_fiber_lowerBound {δ : ℝ} (hδ : 0 < δ)
    {Y : Set ℝ} {X : ℝ → Set ℝ} {y : ℝ} (hy : y ∈ Y)
    (hY : Y ⊆ productLikeUnitGrid δ)
    (hX : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ) :
    ENat.toENNReal (X y).encard ≤
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeIncidenceSet Y X)) := by
  have h_eq := productLikeIncidenceSet_coveringNumber_eq_encard hδ hY hX
  rw [h_eq]
  have h_fiber : ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y} :
      Set (EuclideanSpace ℝ (Fin 2))) ⊆ productLikeIncidenceSet Y X := by
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨y, hy, hz⟩
  have h1 : ENat.toENNReal ({z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ X y ∧ z 1 = y}).encard ≤
      ENat.toENNReal (productLikeIncidenceSet Y X).encard := by
    exact_mod_cast Set.encard_mono h_fiber
  rw [fiber_encard] at h1
  exact h1

end CoveringNumber

section DeltaSetMinSize

/-- A (δ,s,C)-set on the δ-grid in [0,1] has covering number at least 1/(C*δ^s). -/
lemma IsProductLikeRealDeltaSCSet.min_size {δ s C : ℝ} {A : Set ℝ}
    (h : IsProductLikeRealDeltaSCSet δ s C A)
    (hA_grid : A ⊆ productLikeUnitGrid δ)
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hC_pos : 0 < C) :
    ENNReal.ofReal (1 / (C * δ ^ s)) ≤
      ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A)) := by
  rcases h with ⟨hBdd, hNonempty, _, _, _, _, _, _, hMain⟩
  rcases hNonempty with ⟨x, hx⟩
  have h_x0_in_A : x 0 ∈ A := hx
  have h_x0_grid : x 0 ∈ productLikeUnitGrid δ := hA_grid h_x0_in_A
  rcases h_x0_grid.1 with ⟨k, hk⟩
  let k_fn : Fin 1 → ℤ := fun _ => k
  let Q : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube δ k_fn
  have hQ_in : Q ∈ dyadicCubes 1 δ := ⟨k_fn, rfl⟩
  have h_x_in_Q : x ∈ Q := by
    simp only [Q, dyadicCube, Set.mem_setOf_eq]
    intro i
    have h_goal : δ * (k : ℝ) ≤ x 0 ∧ x 0 < δ * ((k : ℝ) + 1) := by
      constructor
      · rw [hk]
      · rw [hk]
        have h : δ * (k : ℝ) < δ * ((k : ℝ) + 1) := by gcongr <;> linarith
        exact h
    fin_cases i
    · exact h_goal
  have h_inter_nonempty : ((productLikeRealLineCopy A) ∩ Q).Nonempty :=
    ⟨x, hx, h_x_in_Q⟩
  have h_unique : ∀ z ∈ (productLikeRealLineCopy A) ∩ Q, z = x := by
    intro z hz
    have hz1 : z 0 ∈ A := hz.1
    have hz2 : z 0 ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := hz.2 0
    have hz3 : z 0 ∈ productLikeUnitGrid δ := hA_grid hz1
    rcases hz3.1 with ⟨m, hm⟩
    have h4 : m = k := by
      rw [hm] at hz2
      have h51 : δ * (k : ℝ) ≤ δ * (m : ℝ) := hz2.1
      have h52 : δ * (m : ℝ) < δ * ((k : ℝ) + 1) := hz2.2
      have h53 : (k : ℝ) ≤ (m : ℝ) := by nlinarith
      have h54 : (m : ℝ) < (k : ℝ) + 1 := by nlinarith
      have h55 : k ≤ m := by exact_mod_cast h53
      have h56 : m < k + 1 := by exact_mod_cast h54
      omega
    have h7 : z 0 = x 0 := by
      rw [hm, h4, hk]
    have h8 : z = x := by
      ext i
      fin_cases i <;> exact h7
    exact h8
  have h_inter_singleton : (productLikeRealLineCopy A) ∩ Q = {x} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact Set.mem_singleton_iff.mpr (h_unique z hz)
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨hx, h_x_in_Q⟩
  have h_cover_one : dyadicCoveringNumber (d := 1) δ ((productLikeRealLineCopy A) ∩ Q) = 1 := by
    rw [h_inter_singleton]
    have h_grid_point : ∀ (z : EuclideanSpace ℝ (Fin 1)), z ∈ ({x} : Set (EuclideanSpace ℝ (Fin 1))) →
        ∀ i : Fin 1, ∃ k : ℤ, z i = δ * (k : ℝ) := by
      intro z hz i
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      rcases h_x0_grid.1 with ⟨k', hk'⟩
      fin_cases i <;> exact ⟨k', hk'⟩
    rw [grid_set_coveringNumber_eq_encard hδ h_grid_point]
    simp
  have h_main2 := hMain hδ_dyadic hQ_in (by linarith) (dyadicScales_le_one hδ_dyadic)
  rw [h_cover_one] at h_main2
  have h3 : ENat.toENNReal (1 : ℕ∞) = 1 := by simp
  rw [h3] at h_main2
  have h4 : 0 < C * δ ^ s := mul_pos hC_pos (Real.rpow_pos_of_pos hδ s)
  have h51 : ENNReal.ofReal C * ENNReal.ofReal (δ ^ s) = ENNReal.ofReal (C * δ ^ s) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  have h_main3 : (1 : ENNReal) ≤
      ENNReal.ofReal (C * δ ^ s) *
        ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A)) := by
    let cov := ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A))
    have h : ENNReal.ofReal C * cov * ENNReal.ofReal (δ ^ s) =
        ENNReal.ofReal (C * δ ^ s) * cov := by
      calc
        ENNReal.ofReal C * cov * ENNReal.ofReal (δ ^ s)
          = ENNReal.ofReal C * (cov * ENNReal.ofReal (δ ^ s)) := by rw [mul_assoc]
        _ = ENNReal.ofReal C * (ENNReal.ofReal (δ ^ s) * cov) := by rw [mul_comm cov]
        _ = (ENNReal.ofReal C * ENNReal.ofReal (δ ^ s)) * cov := by rw [← mul_assoc]
        _ = ENNReal.ofReal (C * δ ^ s) * cov := by rw [h51]
    rw [h] at h_main2
    exact h_main2
  have h7 : ENNReal.ofReal (C * δ ^ s) ≠ 0 := by
    have h71 : 0 < ENNReal.ofReal (C * δ ^ s) := ENNReal.ofReal_pos.mpr h4
    exact h71.ne'
  have h8 : ENNReal.ofReal (1 / (C * δ ^ s)) ≤
      ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A)) := by
    have h_inv : ENNReal.ofReal (1 / (C * δ ^ s)) = (ENNReal.ofReal (C * δ ^ s))⁻¹ := by
      have h9 : (1 / (C * δ ^ s)) = (C * δ ^ s)⁻¹ := by field
      rw [h9]
      exact ofReal_inv_of_pos h4
    rw [h_inv]
    have h10 : (ENNReal.ofReal (C * δ ^ s))⁻¹ ≤
        (ENNReal.ofReal (C * δ ^ s))⁻¹ *
          (ENNReal.ofReal (C * δ ^ s) *
            ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy A))) := by
      exact le_mul_of_one_le_right (by positivity) h_main3
    rw [← mul_assoc, ENNReal.inv_mul_cancel h7 (by simp)] at h10
    <;> simpa [mul_one] using h10
  exact h8

end DeltaSetMinSize

end ProductLikeIncidence
