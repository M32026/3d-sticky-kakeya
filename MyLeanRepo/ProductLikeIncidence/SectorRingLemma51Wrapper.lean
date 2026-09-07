module

/-
# Sector Ring + Lemma 5.1 Wrapper

Composes steps 5–8 of the Phase 2 pipeline, taking sector-normalized data
and a specialized Ring theorem conclusion to produce `False`.

## Pipeline steps

1. **Sector translation** (`sector_translated_graph_theorem`) — translate
   A0 to A = A0 + c ⊆ [1,2], shift G first-coordinate to G_A.
2. **Ring theorem** (`h_ring_spec`) — applied to A ⊆ [1,2] with direction
   Frostman measure ν_dir, produces x ∈ supp(ν_dir) with expansion.
3. **Lemma 5.1** (`lemma51_lower_projection_bound_v2`) — lower bound on
   π_x(G_A) using density, expansion, and difference bounds.
4. **Square-root contradiction** — lower bound from Lemma 5.1 contradicts
   the upper projection bound from the small-P assumption.

## c_proj calibration (exponent ledger)

The per-support graph witness requires TWO bounds on G_t:

**Density (lower):**
  N(G_t) ≥ c_proj · N(B1) · N(B2)

**Small projection (strict upper):**
  N(π_t(G_t)) < (1/2) · (c_proj / (16·K_BSG²)) · δ^{-εgain} · N(B2)

### Density chain

| Stage | Factor | Source |
|-------|--------|--------|
| RoundedGraphAdapter | c_dense / 4 | fjord |
| BSG graph retention | δ^{22q_K} / (16·3^{22}) | indigo |
| FourSectorChart transport | C_chart | cobalt |

Thus: c_proj = C_chart · c_dense · δ^{22q_K} / (64·3^{22})

### Small-projection chain

N(π_t(G_t)) ≤ C_chart_proj · C_proj
where C_proj = δ^{-Lη} · sqrt(N(Pbar)) from the incidence δ-set bound.

### Existence condition

For a valid c_proj, we need:

  N(G_t) / N(π_t(G_t)) > 32·K_BSG² · δ^{εgain} · N(B1)

Substituting the chains and using N(B2) ≈ δ^{-(s-εnc)},
sqrt(N(Pbar)) ≈ δ^{-(s + C_Pbar_loss·η/2)}:

  c_dense · δ^{22q_K + Lη + εnc + C_Pbar_loss·η/2} > 32·K_BSG² · δ^{εgain}

This holds (for δ sufficiently small) when:

  εgain > 22q_K + Lη + εnc + (C_Pbar_loss/2)·η

which is guaranteed by the Ring budget condition
`h_budget : εgain > q_graph + 2·q_diff + q_A + ζ_dir + η_proj`
with q_graph absorbing 22q_K and the chart/projection losses.

### Strictness

The factor 1/2 in the small-projection bound provides the strictness margin.
All constant prefactors (C_chart, C_chart_proj, K_BSG, 3^{22}, etc.) are
absorbed by choosing δ small enough (δ^{positive_exponent} kills constants).

## Sector-genericity

The wrapper is sector-agnostic: `B1` is the set fed to the Ring theorem
(after integer translation to `[1,2]`), and `B2` is the other graph coordinate.
The caller selects the configuration based on the chosen sector:

| Sector | Ring input (B1) | Other coord (B2) |
|--------|-----------------|------------------|
| 0      | B2_original     | B1_original      |
| 1      | B1_original     | B2_original      |
| 2      | -B2_original    | -B1_original     |
| 3      | -B1_original    | -B2_original     |

Negation preserves covering numbers, difference sets, and the grid property,
so all difference bounds and size estimates transfer directly.

The per-direction graph witness `G_t` is supplied by the counter-assumption
applied to `F = E' ∩ (B1_original × B2_original)`, sector-transformed as needed.

## Whiteprint node
`sector_ring_lemma51_wrapper`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.Compat
public import MyLeanRepo.Lemma51Corollary
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.ReduceToStrong_AllScale
public import MyLeanRepo.Fjord.RingExpansionLemma51
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology MeasureTheory Classical

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-! ### Local definitions for first-coordinate translation -/

/-- Translate the first coordinate of a 2D point by c. -/
def shiftFirstCoord (c : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm
    (fun i => if i = 0 then p 0 + c else p 1)

/-- Translate the first coordinate of a 2D set by c. -/
def translateFirstCoord (c : ℝ) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  shiftFirstCoord c '' S

lemma shiftFirstCoord_eval0 (c : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    (shiftFirstCoord c p) 0 = p 0 + c := by
  simp [shiftFirstCoord]

lemma shiftFirstCoord_eval1 (c : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    (shiftFirstCoord c p) 1 = p 1 := by
  simp [shiftFirstCoord]

/-- Projection shift: affineProjection x (translateFirstCoord c G) =
    translateSet (c*x) (affineProjection x G). -/
lemma projection_shift_set {x c : ℝ} {G : Set (EuclideanSpace ℝ (Fin 2))} :
    affineProjection x (translateFirstCoord c G) =
      translateSet (c * x) (affineProjection x G) := by
  ext z
  simp only [affineProjection, Set.mem_image, translateSet]
  constructor
  · rintro ⟨p, hp, h_eq1⟩
    rcases hp with ⟨q, hqG, rfl⟩
    refine ⟨q 0 * x + q 1, ⟨q, hqG, rfl⟩, ?_⟩
    have h_eval : (shiftFirstCoord c q) 0 * x + (shiftFirstCoord c q) 1 =
        (q 0 * x + q 1) + c * x := by
      simp [shiftFirstCoord_eval0, shiftFirstCoord_eval1] <;> ring
    rw [h_eval] at h_eq1
    exact h_eq1
  · rintro ⟨w, ⟨q, hqG, rfl⟩, h_eq3⟩
    refine ⟨shiftFirstCoord c q, ⟨q, hqG, rfl⟩, ?_⟩
    have h_eval : (shiftFirstCoord c q) 0 * x + (shiftFirstCoord c q) 1 =
        (q 0 * x + q 1) + c * x := by
      simp [shiftFirstCoord_eval0, shiftFirstCoord_eval1] <;> ring
    rw [h_eval, h_eq3] <;> ring

/-- Factor-2 covering number bound under arbitrary real translation.

For any bounded `S ⊆ ℝ` and `a : ℝ`, shifting by `a` can at most double
the dyadic covering number, since a shifted δ-interval meets at most two
adjacent δ-dyadic intervals. -/
lemma nreal_translation_factor_two {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Set ℝ} (hS_bdd : IsBounded S) (a : ℝ) :
    Nreal δ (translateSet a S) ≤ 2 * Nreal δ S := by
  let m : ℤ := Int.floor (a / δ)
  have hm1 : δ * (m : ℝ) ≤ a := by
    have h : (m : ℝ) ≤ a / δ := Int.floor_le (a / δ)
    have h' : δ * (m : ℝ) ≤ δ * (a / δ) := by gcongr
    have h'' : δ * (a / δ) = a := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'
  have hm2 : a < δ * ((m : ℝ) + 1) := by
    have h : a / δ < (m : ℝ) + 1 := Int.lt_floor_add_one (a / δ)
    have h' : δ * (a / δ) < δ * ((m : ℝ) + 1) := by gcongr
    have h'' : δ * (a / δ) = a := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'
  let J := realCubeIndexSet δ S
  let K := realCubeIndexSet δ (translateSet a S)
  have hJ_fin : J.Finite := realCubeIndexSet_finite hδ_pos hS_bdd
  have h_main : K ⊆ (fun j : ℤ => j + m) '' J ∪ (fun j : ℤ => j + m + 1) '' J := by
    intro k hk
    rcases (realCubeIndexSet_mem_iff.mp hk) with ⟨y, hyS, hk1, hk2⟩
    rcases hyS with ⟨x, hxS, rfl⟩
    have h_x_in_S : x ∈ S := hxS
    have h_j_exists : ∃ (j : ℤ), j ∈ J ∧ δ * (j : ℝ) ≤ x ∧ x < δ * ((j : ℝ) + 1) := by
      have h_x_in_cube : ∃ (j : ℤ), δ * (j : ℝ) ≤ x ∧ x < δ * ((j : ℝ) + 1) := by
        refine ⟨Int.floor (x / δ), ?_⟩
        have h1 : (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le (x / δ)
        have h2 : x / δ < (Int.floor (x / δ) : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
        constructor
        · calc x = δ * (x / δ) := by field_simp [hδ_pos.ne'] <;> ring
          _ ≥ δ * (Int.floor (x / δ) : ℝ) := by gcongr
        · calc x = δ * (x / δ) := by field_simp [hδ_pos.ne'] <;> ring
          _ < δ * ((Int.floor (x / δ) : ℝ) + 1) := by gcongr
      rcases h_x_in_cube with ⟨j, hj1, hj2⟩
      have hj_in_J : j ∈ J := by
        rw [realCubeIndexSet_mem_iff]
        exact ⟨x, h_x_in_S, hj1, hj2⟩
      exact ⟨j, hj_in_J, hj1, hj2⟩
    rcases h_j_exists with ⟨j, hjJ, hj1, hj2⟩
    have h_k1_int : j + m ≤ k := by
      have h1 : δ * ((j : ℝ) + (m : ℝ)) ≤ x + a := by
        calc δ * ((j : ℝ) + (m : ℝ)) = δ * (j : ℝ) + δ * (m : ℝ) := by ring
        _ ≤ x + a := by linarith
      have h2 : x + a < δ * ((k : ℝ) + 1) := hk2
      have h3 : (j : ℝ) + (m : ℝ) < (k : ℝ) + 1 := by
        have h4 : δ * ((j : ℝ) + (m : ℝ)) < δ * ((k : ℝ) + 1) := by linarith
        nlinarith
      have h5 : (j + m : ℤ) < k + 1 := by exact_mod_cast h3
      exact Int.le_of_lt_add_one h5
    have h_k2_int : k ≤ j + m + 1 := by
      have h1 : δ * (k : ℝ) ≤ x + a := hk1
      have h2 : x + a < δ * ((j : ℝ) + 1) + δ * ((m : ℝ) + 1) := by linarith
      have h3 : δ * (k : ℝ) < δ * ((j : ℝ) + (m : ℝ) + 2) := by
        have h4 : δ * ((j : ℝ) + 1) + δ * ((m : ℝ) + 1) = δ * ((j : ℝ) + (m : ℝ) + 2) := by ring
        rw [h4] at h2; linarith
      have h5 : (k : ℝ) < (j : ℝ) + (m : ℝ) + 2 := by nlinarith
      have h6 : (k : ℝ) < (↑(j + m + 2) : ℝ) := by
        have h7 : (j : ℝ) + (m : ℝ) + 2 = (↑(j + m + 2) : ℝ) := by simp [add_assoc] <;> ring
        rw [h7] at h5; exact h5
      have h8 : k < j + m + 2 := by exact_mod_cast h6
      omega
    have h_k_range : k = j + m ∨ k = j + m + 1 := by
      have h1 : j + m ≤ k := h_k1_int
      have h2 : k ≤ j + m + 1 := h_k2_int
      have h3 : k - (j + m) = 0 ∨ k - (j + m) = 1 := by
        have h4 : 0 ≤ k - (j + m) := by omega
        have h5 : k - (j + m) ≤ 1 := by omega
        interval_cases h6 : k - (j + m) <;> tauto
      rcases h3 with (h3 | h3)
      · left; omega
      · right; omega
    rcases h_k_range with (rfl | rfl)
    · exact Or.inl ⟨j, hjJ, by simp⟩
    · exact Or.inr ⟨j, hjJ, by simp⟩
  have hJ1_fin : ((fun j : ℤ => j + m) '' J).Finite := hJ_fin.image _
  have hJ2_fin : ((fun j : ℤ => j + m + 1) '' J).Finite := hJ_fin.image _
  have hK_fin : K.Finite := hJ1_fin.union hJ2_fin |>.subset h_main
  have h_encard : K.encard ≤ (((fun j : ℤ => j + m) '' J) ∪ ((fun j : ℤ => j + m + 1) '' J)).encard :=
    Set.encard_mono h_main
  have h_union : (((fun j : ℤ => j + m) '' J) ∪ ((fun j : ℤ => j + m + 1) '' J)).encard ≤
      ((fun j : ℤ => j + m) '' J).encard + ((fun j : ℤ => j + m + 1) '' J).encard :=
    Set.encard_union_le _ _
  have h_img1 : ((fun j : ℤ => j + m) '' J).encard = J.encard := by
    apply Set.InjOn.encard_image
    intro j1 _ j2 _ h
    simpa using h
  have h_img2 : ((fun j : ℤ => j + m + 1) '' J).encard = J.encard := by
    apply Set.InjOn.encard_image
    intro j1 _ j2 _ h
    simpa using h
  have h_final : K.encard ≤ 2 * J.encard := by
    calc K.encard
      ≤ (((fun j : ℤ => j + m) '' J) ∪ ((fun j : ℤ => j + m + 1) '' J)).encard := h_encard
    _ ≤ ((fun j : ℤ => j + m) '' J).encard + ((fun j : ℤ => j + m + 1) '' J).encard := h_union
    _ = J.encard + J.encard := by rw [h_img1, h_img2]
    _ = 2 * J.encard := by ring
  have hS_a_bdd : IsBounded (translateSet a S) := by
    have h_lip : LipschitzWith 1 (fun x : ℝ => x + a) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Real.dist_eq] <;> ring_nf <;> exact le_refl _
    exact h_lip.isBounded_image hS_bdd
  have h1 : Nreal δ (translateSet a S) = ENat.toENNReal K.encard :=
    realCoveringNumber_eq_card_ennreal hδ_pos hS_a_bdd
  have h2 : Nreal δ S = ENat.toENNReal J.encard :=
    realCoveringNumber_eq_card_ennreal hδ_pos hS_bdd
  rw [h1, h2]
  exact_mod_cast h_final

/-- Transfer `IsProductLikeRealDeltaSCSet` under translation by an integer `c`.

Since `δ` and every `r ∈ dyadicScales` are of the form `2^{-n}`, an integer `c`
is an integer multiple of both `δ` and `r`.  Therefore:
- translation by `c` preserves dyadic covering numbers at scale `δ` exactly;
- translation by `c` maps `r`-dyadic cubes to `r`-dyadic cubes.

Hence the `(δ, s, C)`-set property transfers with the same constant. -/
lemma real_delta_set_translation_by_int {δ s C : ℝ} {B1 : Set ℝ} {c : ℤ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hB1_bdd : IsBounded B1)
    (hB1_delta : IsProductLikeRealDeltaSCSet δ s C B1) :
    IsProductLikeRealDeltaSCSet δ s C (translateSet (c : ℝ) B1) := by
  dsimp only [IsProductLikeRealDeltaSCSet, productLikeRealLineCopy] at hB1_delta ⊢
  rcases hB1_delta with ⟨hP_bdd, hP_nonempty, h1d, hδ_dy', hδ_pos', hs_nonneg, hs_le_d, hC_pos, h_bound⟩
  let A := translateSet (c : ℝ) B1
  have hA_bdd : IsBounded A := by
    have h_lip : LipschitzWith 1 (fun x : ℝ => x + (c : ℝ)) := by
      apply LipschitzWith.of_dist_le_mul; intro x y
      simp [Real.dist_eq] <;> exact le_refl _
    exact h_lip.isBounded_image hB1_bdd
  have hA_nonempty : A.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    exact ⟨p 0 + (c : ℝ), p 0, hp, by ring⟩
  have hA_bdd' : IsBounded (realLineCopy A) :=
    SetDiscretizationBridge.realLineCopy_bounded_iff.mpr hA_bdd
  have hA_nonempty' : (realLineCopy A).Nonempty := by
    rcases hA_nonempty with ⟨a, ha⟩
    let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => a)
    have hp0 : p 0 = a := by simp [p]
    have h_p_in : p 0 ∈ A := by rw [hp0]; exact ha
    exact ⟨p, h_p_in⟩
  rcases hδ_dyadic with ⟨nδ, hδ_eq⟩
  let mδ : ℤ := c * (2 ^ nδ : ℕ)
  have hcmδ : (c : ℝ) = δ * (mδ : ℝ) := by
    simp [mδ, hδ_eq] <;> field_simp <;> ring
  have hN_A : Nreal δ A = Nreal δ B1 :=
    nreal_translation_by_delta_int hδ_pos hB1_bdd hcmδ
  refine' ⟨hA_bdd', hA_nonempty', h1d, hδ_dy', hδ_pos', hs_nonneg, hs_le_d, hC_pos, _⟩
  intro r Q hr_dyadic hQ_cube hδ_le_r hr_le_one
  have hr_dyadic_copy := hr_dyadic
  rcases hQ_cube with ⟨k, rfl⟩
  let k0 : ℤ := k 0
  rcases hr_dyadic_copy with ⟨nr, hr_eq⟩
  let mr : ℤ := c * (2 ^ nr : ℕ)
  have hcmr : (c : ℝ) = r * (mr : ℝ) := by
    simp [mr, hr_eq] <;> field_simp <;> ring
  let k1 : ℤ := k0 - mr
  let Q' : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r (fun (_ : Fin 1) => k1)
  have hQ'_cube : Q' ∈ dyadicCubes 1 r := ⟨(fun _ => k1), rfl⟩
  let I : Set ℝ := Set.Ico (r * (k0 : ℝ)) (r * ((k0 : ℝ) + 1))
  let I' : Set ℝ := Set.Ico (r * (k1 : ℝ)) (r * ((k1 : ℝ) + 1))
  have hI'_eq : I' = translateSet (-(c : ℝ)) I := by
    ext x
    simp only [I, I', Set.mem_Ico, translateSet, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨x + (c : ℝ), ⟨?_, ?_⟩, by ring⟩
      · have h : r * (k1 : ℝ) + (c : ℝ) = r * (k0 : ℝ) := by simp [k1, hcmr] <;> ring
        linarith
      · have h : r * ((k1 : ℝ) + 1) + (c : ℝ) = r * ((k0 : ℝ) + 1) := by simp [k1, hcmr] <;> ring
        linarith
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have h1 : r * (k1 : ℝ) ≤ y - (c : ℝ) := by
        have h : r * (k1 : ℝ) + (c : ℝ) = r * (k0 : ℝ) := by simp [k1, hcmr] <;> ring
        linarith
      have h2 : y - (c : ℝ) < r * ((k1 : ℝ) + 1) := by
        have h : r * ((k1 : ℝ) + 1) + (c : ℝ) = r * ((k0 : ℝ) + 1) := by simp [k1, hcmr] <;> ring
        linarith
      exact ⟨h1, h2⟩
  have h_eq1 : realLineCopy A ∩ dyadicCube r k = realLineCopy (A ∩ I) := by
    ext x
    simp only [realLineCopy, Set.mem_inter_iff, dyadicCube, Set.mem_setOf_eq, I]
    have h1 : (∀ (i : Fin 1), x i ∈ Set.Ico (r * (k i : ℝ)) (r * ((k i : ℝ) + 1))) ↔ x 0 ∈ I := by
      refine' ⟨fun h => h 0, _⟩
      intro h i
      fin_cases i
      exact h
    constructor
    · rintro ⟨hxA, hcube⟩; exact ⟨hxA, h1.mp hcube⟩
    · rintro ⟨hxA, hI⟩; exact ⟨hxA, h1.mpr hI⟩
  have h_eq2 : realLineCopy B1 ∩ Q' = realLineCopy (B1 ∩ I') := by
    ext x
    simp only [realLineCopy, Set.mem_inter_iff, Q', dyadicCube, Set.mem_setOf_eq, I']
    have h1 : (∀ (i : Fin 1), x i ∈ Set.Ico (r * (k1 : ℝ)) (r * ((k1 : ℝ) + 1))) ↔ x 0 ∈ I' := by
      refine' ⟨fun h => h 0, _⟩
      intro h i
      fin_cases i
      exact h
    constructor
    · rintro ⟨hxA, hcube⟩; exact ⟨hxA, h1.mp hcube⟩
    · rintro ⟨hxA, hI⟩; exact ⟨hxA, h1.mpr hI⟩
  have h_eq3 : A ∩ I = translateSet (c : ℝ) (B1 ∩ I') := by
    ext z
    simp only [A, Set.mem_inter_iff, translateSet, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hzI⟩
      have h_x_in_I' : x ∈ I' := by
        rw [hI'_eq]; exact ⟨x + (c : ℝ), hzI, by ring⟩
      exact ⟨x, ⟨hx, h_x_in_I'⟩, by ring⟩
    · rintro ⟨x, ⟨hx, hxI'⟩, rfl⟩
      have h_y_in_I : x + (c : ℝ) ∈ I := by
        rw [hI'_eq] at hxI'
        rcases hxI' with ⟨w, hwI, h_eq⟩
        have h : x + (c : ℝ) = w := by linarith
        rw [h]; exact hwI
      exact ⟨⟨x, hx, rfl⟩, h_y_in_I⟩
  have hS_bdd : IsBounded (B1 ∩ I') := by
    have h_sub : B1 ∩ I' ⊆ B1 := by intro x hx; exact hx.1
    have h : IsBounded B1 := hB1_bdd
    exact IsBounded.subset hB1_bdd h_sub
  have hAI_bdd : IsBounded (A ∩ I) := by
    have h_sub : A ∩ I ⊆ A := by intro x hx; exact hx.1
    have h : IsBounded A := hA_bdd
    exact IsBounded.subset hA_bdd h_sub
  have h_cov1 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A ∩ dyadicCube r k)) =
      Nreal δ (A ∩ I) := by
    rw [h_eq1] <;> rfl
  have h_cov2 : Nreal δ (A ∩ I) = Nreal δ (B1 ∩ I') := by
    rw [h_eq3]; exact nreal_translation_by_delta_int hδ_pos hS_bdd hcmδ
  have h_cov3 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B1 ∩ Q')) =
      Nreal δ (B1 ∩ I') := by
    rw [h_eq2] <;> rfl
  have h_cov4 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) =
      ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B1)) := by
    have h2 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
    have h3 : Nreal δ B1 = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B1)) := by rfl
    rw [h2, h3] at hN_A; exact hN_A
  have h_bound' := h_bound hr_dyadic hQ'_cube hδ_le_r hr_le_one
  rw [h_cov3] at h_bound'
  rw [h_cov1, h_cov2, h_cov4]
  exact h_bound'

/-- Weaken a Frostman exponent from τ to κ when κ ≤ τ.
For 0 ≤ r ≤ 1, r^τ ≤ r^κ, so the same constant C works. -/
lemma weaken_frostman_exponent {δ τ κ C : ℝ} {μ : Measure ℝ}
    (hκ_le_τ : κ ≤ τ) (hδ_pos : 0 < δ)
    (hν : IsDirectionFrostman δ τ C μ) :
    IsDirectionFrostman δ κ C μ := by
  have h1 : μ Set.univ = 1 := hν.1
  have h2 : μ.support ⊆ Set.Icc (0 : ℝ) 1 := hν.2.1
  have h3 : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C * r ^ κ) := by
    intro a r hδ_le_r hr_le_one
    have h4 : μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C * r ^ τ) :=
      hν.2.2 a r hδ_le_r hr_le_one
    have hr_pos : 0 < r := by linarith
    have h5 : r ^ τ ≤ r ^ κ :=
      Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hκ_le_τ
    by_cases hC : 0 ≤ C
    · have h8 : C * r ^ τ ≤ C * r ^ κ := by gcongr
      have h9 : ENNReal.ofReal (C * r ^ τ) ≤ ENNReal.ofReal (C * r ^ κ) :=
        ENNReal.ofReal_le_ofReal h8
      exact le_trans h4 h9
    · have hC_neg : C < 0 := by linarith
      have h10 : C * r ^ τ ≤ 0 := by exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      have h11 : C * r ^ κ ≤ 0 := by exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      have h12 : ENNReal.ofReal (C * r ^ τ) = 0 := by
        rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
      have h13 : ENNReal.ofReal (C * r ^ κ) = 0 := by
        rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
      rw [h12] at h4
      rw [h13]
      exact h4
  exact ⟨h1, h2, h3⟩

theorem sector_ring_lemma51_wrapper
    {δ s τ κ0 η εnc εgain : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_le_one : δ ≤ 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hκ0_pos : 0 < κ0) (hκ0_lt_s : κ0 < s)
    (hκ0_le_tau : κ0 ≤ τ)
    (hη_pos : 0 < η)
    {q_graph q_diff q_A ζ_dir η_proj : ℝ}
    (h_q_graph_nonneg : 0 ≤ q_graph)
    (h_q_diff_nonneg : 0 ≤ q_diff)
    (h_q_A_nonneg : 0 ≤ q_A)
    (hζ_dir_nonneg : 0 ≤ ζ_dir)
    (hη_proj_nonneg : 0 ≤ η_proj)
    (h_budget : εgain > q_graph + 2 * q_diff + q_A + ζ_dir + η_proj)
    {K_work : ℝ}
    (hK_work_ge1 : 1 ≤ K_work)
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
        Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
        ∃ x ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x * b) A A))
    -- Sector-generic: B1 is the Ring input set, B2 is the other coordinate.
    -- For different sectors, the caller sets B1,B2 to B1_original, B2_original,
    -- their negations, or swaps them.  No sector-specific assumptions are made.
    {B1 B2 : Set ℝ}
    (hB1_bdd : IsBounded B1) (hB2_bdd : IsBounded B2)
    (hB1_nonempty : B1.Nonempty) (hB2_nonempty : B2.Nonempty)
    (c : ℤ)
    (hA_range : translateSet (↑c) B1 ⊆ Set.Icc (1 : ℝ) 2)
    (hB1_grid : ∀ b ∈ B1, ∃ k : ℤ, b = δ * (k : ℝ))
    (hB2_grid : ∀ b ∈ B2, ∃ k : ℤ, b = δ * (k : ℝ))
    {c_proj : ℝ}
    (hc_proj_pos : 0 < c_proj)
    {K_BSG : ℝ}
    (hK_BSG_pos : 0 < K_BSG)
    (h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤
        ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_diff2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
        ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_size_upper : Nreal δ B1 ≤
        ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB1_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) B1)
    {ν_dir : Measure ℝ}
    (hν_frost : IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) ν_dir)
    -- Per-support graph witness family
    (h_graph_witness : ∀ (t : ℝ), t ∈ ν_dir.support →
      ∃ (G_t : Set (EuclideanSpace ℝ (Fin 2))),
        IsBounded G_t ∧
        (∀ p ∈ G_t, p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
        (∀ p ∈ G_t, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
        ENat.toENNReal (dyadicCoveringNumber δ G_t) ≥
          ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 ∧
        ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_t)) <
          (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
            ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2) :
    False := by
  let A : Set ℝ := translateSet (c : ℝ) B1
  have hA_bdd : IsBounded A := by
    have h_lip : LipschitzWith 1 (fun x : ℝ => x + (c : ℝ)) := by
      apply LipschitzWith.of_dist_le_mul; intro x y
      simp [Real.dist_eq] <;> exact le_refl _
    exact h_lip.isBounded_image hB1_bdd
  have hA_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A :=
    real_delta_set_translation_by_int hδ_pos hδ_dyadic hB1_bdd hB1_delta_kappa
  rcases dyadic_one_is_delta_mul_int hδ_dyadic with ⟨m1, hm1⟩
  let m : ℤ := c * m1
  have hcm : (c : ℝ) = δ * (m : ℝ) := by
    have h2 : (m : ℝ) = (c : ℝ) * (m1 : ℝ) := by simp [m] <;> norm_cast <;> ring
    calc (c : ℝ)
      = (c : ℝ) * 1 := by ring
    _ = (c : ℝ) * (δ * (m1 : ℝ)) := by rw [hm1]
    _ = δ * ((c : ℝ) * (m1 : ℝ)) := by ring
    _ = δ * (m : ℝ) := by rw [h2]
  have hN_A_eq : Nreal δ A = Nreal δ B1 :=
    nreal_translation_by_delta_int hδ_pos hB1_bdd hcm
  have h_size_upper_A : Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    rw [hN_A_eq]; exact h_size_upper
  have hA_eq : A = translateSet (c : ℝ) B1 := by rfl
  have hA_range' : A ⊆ Set.Icc (1 : ℝ) 2 := by
    rw [hA_eq]
    exact hA_range
  -- Step 1: Ring theorem chooses t ∈ support
  have h_ring_result : ∃ (t : ℝ), t ∈ ν_dir.support ∧
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
        Nreal δ (Set.image2 (fun a b => a + t * b) A A) :=
    h_ring_spec A ν_dir hA_range' hA_delta_kappa h_size_upper_A hν_frost
  rcases h_ring_result with ⟨t, ht_support, h_expansion⟩
  -- Step 2: Get graph witness G_t for this t
  rcases h_graph_witness t ht_support with
    ⟨G_t, hG_t_bdd, hG_t_sub, hG_t_grid, hG_t_dense, h_proj_upper_t⟩
  -- Step 3: Translate G_t to G_A_t
  let G_A_t : Set (EuclideanSpace ℝ (Fin 2)) := translateFirstCoord (c : ℝ) G_t
  -- c = δ * m
  rcases dyadic_one_is_delta_mul_int hδ_dyadic with ⟨m1, hm1⟩
  let m : ℤ := c * m1
  have hcm : (c : ℝ) = δ * (m : ℝ) := by
    have h2 : (m : ℝ) = (c : ℝ) * (m1 : ℝ) := by simp [m] <;> norm_cast <;> ring
    calc (c : ℝ)
      = (c : ℝ) * 1 := by ring
    _ = (c : ℝ) * (δ * (m1 : ℝ)) := by rw [hm1]
    _ = δ * ((c : ℝ) * (m1 : ℝ)) := by ring
    _ = δ * (m : ℝ) := by rw [h2]
  have h_neg_c : -(c : ℝ) = δ * ((-m : ℤ) : ℝ) := by
    rw [hcm] <;> simp <;> ring
  -- G_A_t properties
  have hGA_t_bdd : IsBounded G_A_t := by
    have h_lip : LipschitzWith 1 (shiftFirstCoord (c : ℝ)) := by
      apply LipschitzWith.of_dist_le_mul; intro p q
      simp [EuclideanSpace.dist_eq, Fin.sum_univ_two,
        shiftFirstCoord_eval0, shiftFirstCoord_eval1, Real.dist_eq]
      <;> rw [Real.sqrt_sq_eq_abs] <;> ring
    exact h_lip.isBounded_image hG_t_bdd
  have hGA_t_sub : ∀ p ∈ G_A_t, p 0 ∈ A ∧ p 1 ∈ B2 := by
    intro p hp
    rcases hp with ⟨q, hqG, rfl⟩
    have hq_sub : q 0 ∈ B1 ∧ q 1 ∈ B2 := hG_t_sub q hqG
    constructor
    · simp only [shiftFirstCoord_eval0, translateSet, Set.mem_image]
      exact ⟨q 0, hq_sub.1, by ring⟩
    · simpa [shiftFirstCoord_eval1] using hq_sub.2
  have hGA_t_grid : ∀ p ∈ G_A_t, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ) := by
    intro p hp i
    rcases hp with ⟨q, hqG, rfl⟩
    fin_cases i
    · rcases hG_t_grid q hqG 0 with ⟨k, hk⟩
      refine ⟨k + m, ?_⟩
      simp [shiftFirstCoord_eval0, hk, hcm] <;> ring
    · exact hG_t_grid q hqG 1
  have h_shift_inj : Function.Injective (shiftFirstCoord (c : ℝ)) := by
    intro p q h
    have h0 : (shiftFirstCoord (c : ℝ) p) 0 = (shiftFirstCoord (c : ℝ) q) 0 := by rw [h]
    have h1 : (shiftFirstCoord (c : ℝ) p) 1 = (shiftFirstCoord (c : ℝ) q) 1 := by rw [h]
    have p0 : p 0 = q 0 := by
      have h_eq : p 0 + (c : ℝ) = q 0 + (c : ℝ) := by
        simpa [shiftFirstCoord_eval0] using h0
      linarith
    have p1 : p 1 = q 1 := by
      simpa [shiftFirstCoord_eval1] using h1
    ext i; fin_cases i <;> tauto
  have hN_GA_t_eq : ENat.toENNReal (dyadicCoveringNumber δ G_A_t) =
      ENat.toENNReal (dyadicCoveringNumber δ G_t) := by
    have h1 : dyadicCoveringNumber δ G_t = G_t.encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hG_t_grid
    have h2 : dyadicCoveringNumber δ G_A_t = G_A_t.encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hGA_t_grid
    have h3 : G_A_t.encard = G_t.encard := by
      have h_inj : Set.InjOn (shiftFirstCoord (c : ℝ)) G_t := by
        intro x _ y _ h; exact h_shift_inj h
      exact h_inj.encard_image
    rw [h2, h1, h3]
  have hG_A_t_dense : ENat.toENNReal (dyadicCoveringNumber δ G_A_t) ≥
      ENNReal.ofReal c_proj * Nreal δ A * Nreal δ B2 := by
    rw [hN_GA_t_eq]
    have hN_A_eq : Nreal δ A = Nreal δ B1 :=
      nreal_translation_by_delta_int hδ_pos hB1_bdd hcm
    rw [hN_A_eq]
    exact hG_t_dense
  -- Difference bounds for A
  have h_mem_iff : ∀ (z : ℝ), z ∈ A ↔ z - (c : ℝ) ∈ B1 := by
    intro z
    constructor
    · intro hz
      have h : z + (-(c : ℝ)) ∈ B1 := by simpa [A, translateSet] using hz
      have h' : z + (-(c : ℝ)) = z - (c : ℝ) := by ring
      rw [h'] at h
      exact h
    · intro hb
      have h' : z - (c : ℝ) = z + (-(c : ℝ)) := by ring
      rw [h'] at hb
      simpa [A, translateSet] using hb
  have hAA_eq : Set.image2 (· - ·) A A = Set.image2 (· - ·) B1 B1 := by
    ext z
    simp only [Set.mem_image2]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      have hbx : x - (c : ℝ) ∈ B1 := (h_mem_iff x).mp hx
      have hby : y - (c : ℝ) ∈ B1 := (h_mem_iff y).mp hy
      exact ⟨x - (c : ℝ), hbx, y - (c : ℝ), hby, by ring⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      have h1 : x + (c : ℝ) ∈ A := (h_mem_iff (x + (c : ℝ))).mpr (by simpa using hx)
      have h2 : y + (c : ℝ) ∈ A := (h_mem_iff (y + (c : ℝ))).mpr (by simpa using hy)
      exact ⟨x + (c : ℝ), h1, y + (c : ℝ), h2, by ring⟩
  have hB2B1_bdd : IsBounded (Set.image2 (· - ·) B2 B1) := by
    exact bounded_image2_sub hB2_bdd hB1_bdd
  have hB2A_eq : Set.image2 (· - ·) B2 A =
      translateSet (-(c : ℝ)) (Set.image2 (· - ·) B2 B1) := by
    ext z
    simp only [Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      have hb : y - (c : ℝ) ∈ B1 := (h_mem_iff y).mp hy
      refine ⟨x - (y - (c : ℝ)), ?_, ?_⟩
      · simp only [Set.mem_image2]
        exact ⟨x, hx, y - (c : ℝ), hb, by ring⟩
      · linarith
    · rintro ⟨w, hw, rfl⟩
      rcases Set.mem_image2.mp hw with ⟨x, hx, b, hb, rfl⟩
      have h1 : b + (c : ℝ) ∈ A := (h_mem_iff (b + (c : ℝ))).mpr (by simpa using hb)
      simp only [Set.mem_image2]
      exact ⟨x, hx, b + (c : ℝ), h1, by ring⟩
  have h_diff1_A : Nreal δ (Set.image2 (· - ·) A A) ≤
      ENNReal.ofReal K_BSG * Nreal δ A := by
    rw [hAA_eq]
    have hN_A_eq : Nreal δ A = Nreal δ B1 :=
      nreal_translation_by_delta_int hδ_pos hB1_bdd hcm
    rw [hN_A_eq]; exact h_diff1
  have h_diff2_A : Nreal δ (Set.image2 (· - ·) B2 A) ≤
      ENNReal.ofReal K_BSG * Nreal δ A := by
    rw [hB2A_eq]
    have hN_trans : Nreal δ (translateSet (-(c : ℝ)) (Set.image2 (· - ·) B2 B1)) =
        Nreal δ (Set.image2 (· - ·) B2 B1) :=
      nreal_translation_by_delta_int hδ_pos hB2B1_bdd h_neg_c
    rw [hN_trans]
    have hN_A_eq : Nreal δ A = Nreal δ B1 :=
      nreal_translation_by_delta_int hδ_pos hB1_bdd hcm
    rw [hN_A_eq]; exact h_diff2
  -- Step 4: N(A) positivity and non-top
  have hA_nonempty : A.Nonempty := hB1_nonempty.image (fun x => x + (c : ℝ))
  have hN_A_pos : 0 < Nreal δ A := by
    have hRL_nonempty : (realLineCopy A).Nonempty := by
      rcases hA_nonempty with ⟨a, ha⟩
      let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => a)
      have hp0 : p 0 = a := by simp [p]
      exact ⟨p, by simpa [realLineCopy, hp0] using ha⟩
    have h1 : 0 < dyadicCoveringNumber δ (realLineCopy A) :=
      robust_projection.dyadic_covering_number_pos hδ_pos hRL_nonempty
    have h2 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
    rw [h2]
    have hne : (dyadicCoveringNumber δ (realLineCopy A)) ≠ 0 := h1.ne'
    have h3 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) ≠ 0 := by exact_mod_cast hne
    exact h3.bot_lt
  have hN_A_ne_top : Nreal δ A ≠ ⊤ :=
    WeakTwoEndsSumProduct.Nreal_ne_top hδ_pos hA_bdd
  -- Step 5: Apply Lemma 5.1
  have h_lemma51 : ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 ≤
      ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_A_t)) := by
    exact lemma51_lower_projection_bound_corrected (s := s)
      (hδ_pos := hδ_pos)
      (hx_abs := by
        have h1 : ν_dir.support ⊆ Set.Icc (0 : ℝ) 1 := hν_frost.2.1
        have h2 : t ∈ Set.Icc (0 : ℝ) 1 := h1 ht_support
        exact abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩)
      (hB1_bdd := hA_bdd)
      (hB2_bdd := hB2_bdd)
      (hG_bdd := hGA_t_bdd)
      (hG_sub := hGA_t_sub)
      (hG_dense := hG_A_t_dense)
      (h_expansion := h_expansion)
      (h_diff1 := h_diff1_A)
      (h_diff2 := h_diff2_A)
      (hN_B1_pos := hN_A_pos)
      (hN_B1_ne_top := hN_A_ne_top)
      (hc_proj_pos := hc_proj_pos)
      (hK_BSG_pos := hK_BSG_pos)
      (hεgain_pos := by
        have h_sum_nonneg : 0 ≤ q_graph + 2 * q_diff + q_A + ζ_dir + η_proj := by positivity
        linarith [h_budget, h_sum_nonneg])
  -- Step 6: Projection shift and factor-2 contradiction
  have h_set_eq : affineProjection t G_A_t =
      translateSet ((c : ℝ) * t) (affineProjection t G_t) := by
    exact projection_shift_set (G := G_t)
  have hS_bdd : IsBounded (affineProjection t G_t) := by
    let f : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * t + p 1
    let K : NNReal := ⟨|t| + 1, by positivity⟩
    have h_lip : LipschitzWith K f := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      have h1 : dist (f p) (f q) = |f p - f q| := by simp [Real.dist_eq]
      rw [h1]
      have h_expand : f p - f q = (p 0 - q 0) * t + (p 1 - q 1) := by
        simp only [f] <;> ring
      rw [h_expand]
      have h3 : |(p 0 - q 0) * t + (p 1 - q 1)| ≤ |t| * |p 0 - q 0| + |p 1 - q 1| := by
        have h_abs : |(p 0 - q 0) * t + (p 1 - q 1)| ≤ |(p 0 - q 0) * t| + |p 1 - q 1| := by exact abs_add_le ((p.ofLp 0 - q.ofLp 0) * t) (p.ofLp 1 - q.ofLp 1)
        have h_mul : |(p 0 - q 0) * t| = |t| * |p 0 - q 0| := by rw [abs_mul] <;> ring
        rw [h_mul] at h_abs; exact h_abs
      have h4 : |p 0 - q 0| ≤ dist p q := by exact ProductMeasureEnergy.coord_le_dist 0
      have h5 : |p 1 - q 1| ≤ dist p q := by exact ProductMeasureEnergy.coord_le_dist 1
      calc |(p 0 - q 0) * t + (p 1 - q 1)|
        ≤ |t| * |p 0 - q 0| + |p 1 - q 1| := h3
      _ ≤ |t| * dist p q + dist p q := by gcongr
      _ = (|t| + 1) * dist p q := by ring
    exact h_lip.isBounded_image hG_t_bdd
  have hN_factor_two : Nreal δ (affineProjection t G_A_t) ≤ 2 * Nreal δ (affineProjection t G_t) := by
    rw [h_set_eq]
    exact nreal_translation_factor_two hδ_pos hS_bdd ((c : ℝ) * t)
  let L : ENNReal := ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_A_t)) =
      Nreal δ (affineProjection t G_A_t) := by rfl
  have h2 : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_t)) =
      Nreal δ (affineProjection t G_t) := by rfl
  have h_proj_le : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_A_t)) ≤
      2 * ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_t)) := by
    rw [h1, h2]; exact hN_factor_two
  have hL : L ≤ ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_A_t)) := h_lemma51
  set N_G : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D t G_t)) with hN_G_def
  have hU : N_G < (1 / 2 : ENNReal) * L := by
    have h_eq : (1 / 2 : ENNReal) * L =
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 := by
      simp [L, mul_assoc] <;> ring
    rw [h_eq]
    exact h_proj_upper_t
  have hL_finite : L ≠ ⊤ := by
    apply mul_ne_top
    · apply mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact WeakTwoEndsSumProduct.Nreal_ne_top hδ_pos hB2_bdd
  have h_half : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
    have h1 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    rw [h1]
    have h2 : (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (1 : ℝ) := by
      have h3 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
      rw [h3, ← ENNReal.ofReal_mul (by norm_num)] <;> norm_num
    rw [h2] <;> simp
  have h_double : 2 * ((1 / 2 : ENNReal) * L) = L := by
    have h1 : 2 * ((1 / 2 : ENNReal) * L) = ((2 : ENNReal) * (1 / 2 : ENNReal)) * L := by rw [mul_assoc]
    rw [h1, h_half, one_mul]
  have h10 : 2 * N_G < L := by
    have h_pos2 : (0 : ENNReal) < 2 := by norm_num
    have h_ne_top2 : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h_strict : 2 * N_G < 2 * ((1 / 2 : ENNReal) * L) :=
      ENNReal.mul_lt_mul_right h_pos2.ne' h_ne_top2 hU
    rw [h_double] at h_strict
    exact h_strict
  have h11 : L ≤ 2 * N_G := le_trans hL h_proj_le
  exact not_le.mpr h10 h11

end ProductLikeIncidence.ProductReduction
