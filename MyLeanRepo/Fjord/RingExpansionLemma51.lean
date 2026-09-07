module

/-
# Ring Expansion via Translation to [1,2] — No Loss Approach

Phase 2, Step 6: Apply the ring theorem `h_ring_spec` to B1 ⊆ [0,1]
by translating to A = B1 + 1 ⊆ [1,2], and returning A directly.

## Key insight

Since δ ∈ dyadicScales, 1 = 2^n · δ is an integer multiple of δ.
Therefore translation by 1 preserves ALL dyadic covering numbers EXACTLY:
- Nreal δ (B1 + 1) = Nreal δ B1
- IsProductLikeRealDeltaSCSet is preserved
- Difference sets: (B1+1) - (B1+1) = B1 - B1 exactly

By returning A (not translating the expansion back to B1), we avoid
any factor-2 loss.

## Dependencies

Translation lemmas proved by Onyx:
- `dyadic_one_is_delta_mul_int`
- `nreal_translation_by_delta_int`
- `delta_set_add_one`

## Whiteprint node

`ring_expansion_A`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.Lemma51Corollary
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal MeasureTheory Bornology

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- Translate a real set by c: `{x + c | x ∈ S}`. -/
def translateSet (c : ℝ) (S : Set ℝ) : Set ℝ := (fun x => x + c) '' S

/-! ========================================================================
   Translation lemmas (proved by Onyx)
-/

/-- For δ ∈ dyadicScales, ∃ m : ℤ such that 1 = δ * (m : ℝ). -/
lemma dyadic_one_is_delta_mul_int {δ : ℝ} (hδ : δ ∈ dyadicScales) :
    ∃ (m : ℤ), 1 = δ * (m : ℝ) := by
  rcases hδ with ⟨n, hn⟩
  have hδ_pos : 0 < δ := by rw [hn]; positivity
  have h1 : δ = 1 / (2 : ℝ) ^ n := by
    rw [hn]
    have h2 : (2 : ℝ) ^ (-(n : ℤ)) = 1 / (2 : ℝ) ^ n := by
      have h3 : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by
        rw [zpow_neg] <;> simp
      rw [h3] <;> field_simp
    exact h2
  let m : ℤ := ↑(2 ^ n : ℕ)
  have h2 : (m : ℝ) = (2 : ℝ) ^ n := by simp [m] <;> norm_cast
  have h3 : 1 = δ * (m : ℝ) := by
    rw [h1, h2]; field_simp <;> ring
  exact ⟨m, h3⟩

/-- If c = δ * m for some m : ℤ, then Nreal δ (translateSet c S) = Nreal δ S. -/
lemma nreal_translation_by_delta_int {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Set ℝ} (hS_bdd : IsBounded S) {m : ℤ} {c : ℝ} (hc : c = δ * (m : ℝ)) :
    Nreal δ (translateSet c S) = Nreal δ S := by
  have h_lip : LipschitzWith 1 (fun x : ℝ => x + c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y; simp [Real.dist_eq] <;> ring_nf <;> exact le_refl _
  have hS'_bdd : IsBounded (translateSet c S) := h_lip.isBounded_image hS_bdd
  let idxS := bourgain_projection_theorem.realCubeIndexSet δ S
  let idxSc := bourgain_projection_theorem.realCubeIndexSet δ (translateSet c S)
  have h1 : idxSc = (fun k : ℤ => k + m) '' idxS := by
    ext j
    simp only [bourgain_projection_theorem.realCubeIndexSet, Set.mem_setOf_eq,
      Set.mem_image, translateSet]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, x, hxS, rfl⟩
      have h_cast : ((j - m : ℤ) : ℝ) = (j : ℝ) - (m : ℝ) := by simp
      have h_x_in : x ∈ Set.Ico (δ * ((j - m : ℤ) : ℝ)) (δ * (((j - m : ℤ) : ℝ) + 1)) := by
        rw [h_cast]
        have h_eq1 : δ * ((j : ℝ) - (m : ℝ)) = δ * (j : ℝ) - c := by
          simp [hc] <;> ring
        have h_eq2 : δ * (((j : ℝ) - (m : ℝ)) + 1) = δ * ((j : ℝ) + 1) - c := by
          simp [hc] <;> ring
        rw [h_eq1, h_eq2]; exact ⟨by linarith, by linarith⟩
      refine ⟨j - m, ⟨x, h_x_in, hxS⟩, by simp⟩
    · rintro ⟨k, ⟨x, hxIco, hxS⟩, rfl⟩
      refine ⟨x + c, ⟨?_, ?_⟩, x, hxS, by ring⟩
      · have h_cast : ((k + m : ℤ) : ℝ) = (k : ℝ) + (m : ℝ) := by simp
        have h : δ * ((k + m : ℤ) : ℝ) = δ * (k : ℝ) + c := by
          rw [h_cast]; simp [hc] <;> ring
        rw [h]; linarith [hxIco.1]
      · have h_cast : ((k + m : ℤ) : ℝ) = (k : ℝ) + (m : ℝ) := by simp
        have h : δ * (((k + m : ℤ) : ℝ) + 1) = δ * ((k : ℝ) + 1) + c := by
          rw [h_cast]; simp [hc] <;> ring
        rw [h]; linarith [hxIco.2]
  have h_finS : idxS.Finite :=
    bourgain_projection_theorem.realCubeIndexSet_finite hδ_pos hS_bdd
  have h_inj' : Set.InjOn (fun k : ℤ => k + m) idxS := by
    intro k1 _ k2 _ h; simpa using h
  have h2 : idxSc.encard = idxS.encard := by
    rw [h1]; exact Set.InjOn.encard_image h_inj'
  have hN1 : Nreal δ (translateSet c S) = ENat.toENNReal idxSc.encard := by
    have h : Nreal δ (translateSet c S) = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (translateSet c S))) := by rfl
    rw [h]
    have h_line : realLineCopy (translateSet c S) = productLikeRealLineCopy (translateSet c S) := by rfl
    rw [h_line]
    exact bourgain_projection_theorem.realCoveringNumber_eq_card hδ_pos hS'_bdd
  have hN2 : Nreal δ S = ENat.toENNReal idxS.encard := by
    have h : Nreal δ S = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy S)) := by rfl
    rw [h]
    have h_line : realLineCopy S = productLikeRealLineCopy S := by rfl
    rw [h_line]
    exact bourgain_projection_theorem.realCoveringNumber_eq_card hδ_pos hS_bdd
  rw [hN1, hN2, h2]

/-- For dyadic δ, if S is a (δ, s, C)-set, then translateSet 1 S is also. -/
lemma delta_set_add_one {δ s C : ℝ} {S : Set ℝ}
    (hδ_dyadic : δ ∈ dyadicScales)
    (h : IsProductLikeRealDeltaSCSet δ s C S) :
    IsProductLikeRealDeltaSCSet δ s C (translateSet 1 S) := by
  let pt : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun y => (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
  have hpt_eval : ∀ (y : ℝ), (pt y) 0 = y := by
    intro y; simp [pt]
  let P : Set (EuclideanSpace ℝ (Fin 1)) := productLikeRealLineCopy S
  have h_delta : IsDeltaSCSet (d := 1) δ s C P := h
  rcases h_delta with ⟨h_bdd, h_nonempty, h_d, hδ_scale, hδ_pos, hs_nonneg, hs_le, hC_pos, h_main⟩
  have h_proj_lip : LipschitzWith 1 (fun (x : EuclideanSpace ℝ (Fin 1)) => x 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [EuclideanSpace.dist_eq, Fin.sum_univ_one] <;> exact le_refl _
  have hS_bdd_real : IsBounded S := by
    have hS_eq : S = (fun (x : EuclideanSpace ℝ (Fin 1)) => x 0) '' P := by
      ext y
      simp only [P, productLikeRealLineCopy, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨pt y, h, hpt_eval y⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [hS_eq]
    exact h_proj_lip.isBounded_image h_bdd
  have h_emb_lip : LipschitzWith 1 pt := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h : dist (pt x) (pt y) = |x - y| := by
      simp [pt, EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq]
      <;> rw [Real.sqrt_sq_eq_abs]
    rw [h]
    <;> simp [Real.dist_eq] <;> exact le_refl _
  have h_trans_bdd : IsBounded (translateSet 1 S) := by
    have h_lip : LipschitzWith 1 (fun x : ℝ => x + 1) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [Real.dist_eq] <;> exact le_refl _
    exact h_lip.isBounded_image hS_bdd_real
  let P1 : Set (EuclideanSpace ℝ (Fin 1)) := productLikeRealLineCopy (translateSet 1 S)
  have hP1_eq : P1 = pt '' (translateSet 1 S) := by
    ext z
    simp only [P1, productLikeRealLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro h
      have hz : pt (z 0) = z := by
        ext i; fin_cases i <;> simp [pt, hpt_eval]
      exact ⟨z 0, h, hz⟩
    · rintro ⟨y, hy, rfl⟩
      have h7 : (pt y) 0 ∈ translateSet 1 S := by
        rw [hpt_eval y]; exact hy
      exact h7
  have h1_bdd : IsBounded P1 := by
    rw [hP1_eq]
    exact h_emb_lip.isBounded_image h_trans_bdd
  have h1_nonempty : P1.Nonempty := by
    rcases h_nonempty with ⟨x, hx⟩
    have h_x_in : x 0 ∈ S := hx
    have h_goal : (pt (x 0 + 1)) 0 ∈ translateSet 1 S := by
      have h6 : (pt (x 0 + 1)) 0 = x 0 + 1 := hpt_eval (x 0 + 1)
      rw [h6]
      exact ⟨x 0, h_x_in, by ring⟩
    have h_main_goal : pt (x 0 + 1) ∈ P1 := by
      exact h_goal
    exact ⟨pt (x 0 + 1), h_main_goal⟩
  rcases dyadic_one_is_delta_mul_int hδ_dyadic with ⟨mδ, hmδ⟩
  have h_translate_Nreal : ∀ (A : Set ℝ), IsBounded A → Nreal δ (translateSet 1 A) = Nreal δ A := by
    intro A hA
    exact nreal_translation_by_delta_int hδ_pos hA hmδ
  refine ⟨h1_bdd, h1_nonempty, h_d, hδ_scale, hδ_pos, hs_nonneg, hs_le, hC_pos, ?_⟩
  intro r Q hr hQ hδr hr1
  rcases hQ with ⟨k, hk⟩
  let k0 : ℤ := k 0
  have hr_dyadic : r ∈ dyadicScales := hr
  rcases dyadic_one_is_delta_mul_int hr_dyadic with ⟨mr, hmr⟩
  let k' : Fin 1 → ℤ := fun _ => k0 - mr
  let Q' : Set (EuclideanSpace ℝ (Fin 1)) := dyadicCube r k'
  have hQ'_in : Q' ∈ dyadicCubes 1 r := ⟨k', rfl⟩
  let I_Q : Set ℝ := Set.Ico (r * (k0 : ℝ)) (r * ((k0 : ℝ) + 1))
  let I_Q' : Set ℝ := Set.Ico (r * ((k0 - mr : ℤ) : ℝ)) (r * (((k0 - mr : ℤ) : ℝ) + 1))
  have h_Q_eq : Q = productLikeRealLineCopy I_Q := by
    rw [hk]
    ext x
    simp only [productLikeRealLineCopy, dyadicCube, Set.mem_setOf_eq, I_Q]
    <;> aesop
  have h_Q'_eq : Q' = productLikeRealLineCopy I_Q' := by
    ext x
    simp only [Q', productLikeRealLineCopy, dyadicCube, Set.mem_setOf_eq, I_Q']
    <;> aesop
  have h_interval_shift : I_Q' = {x : ℝ | x + 1 ∈ I_Q} := by
    ext x
    simp only [I_Q, I_Q', Set.mem_setOf_eq, Set.mem_Ico]
    have h1 : r * ((k0 - mr : ℤ) : ℝ) = r * (k0 : ℝ) - 1 := by
      simp [hmr] <;> ring
    have h2 : r * (((k0 - mr : ℤ) : ℝ) + 1) = r * ((k0 : ℝ) + 1) - 1 := by
      simp [hmr] <;> ring
    rw [h1, h2]
    constructor <;> intro h <;> constructor <;> linarith
  have h_set_eq : (translateSet 1 S) ∩ I_Q = translateSet 1 (S ∩ I_Q') := by
    ext y
    simp only [translateSet, Set.mem_inter_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, hyI⟩
      have h_x_in' : x ∈ I_Q' := by
        rw [h_interval_shift]
        simpa using hyI
      exact ⟨x, ⟨hxS, h_x_in'⟩, by ring⟩
    · rintro ⟨x, ⟨hxS, hxI'⟩, rfl⟩
      have h_y_in_IQ : x + 1 ∈ I_Q := by
        rw [h_interval_shift] at hxI'
        exact hxI'
      exact ⟨⟨x, hxS, by ring⟩, h_y_in_IQ⟩
  have h_intersection1 : P1 ∩ Q = productLikeRealLineCopy ((translateSet 1 S) ∩ I_Q) := by
    rw [h_Q_eq]
    ext x
    simp only [P1, productLikeRealLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq]
    <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
  have h_intersection2 : P ∩ Q' = productLikeRealLineCopy (S ∩ I_Q') := by
    rw [h_Q'_eq]
    ext x
    simp only [P, productLikeRealLineCopy, Set.mem_inter_iff, Set.mem_setOf_eq]
    <;> constructor <;> intro h <;> exact ⟨h.1, h.2⟩
  have hSIQ'_bdd : IsBounded (S ∩ I_Q') := by
    have h_sub : S ∩ I_Q' ⊆ S := by intro x hx; exact hx.1
    exact hS_bdd_real.subset h_sub
  have hP1_inter_bdd : IsBounded (P1 ∩ Q) := by
    have h_sub : P1 ∩ Q ⊆ P1 := by intro x hx; exact hx.1
    exact h1_bdd.subset h_sub
  have h_cover1 : ENat.toENNReal (dyadicCoveringNumber δ (P1 ∩ Q)) =
      ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q')) := by
    rw [h_intersection1, h_set_eq, h_intersection2]
    have hN_eq : Nreal δ (translateSet 1 (S ∩ I_Q')) = Nreal δ (S ∩ I_Q') :=
      h_translate_Nreal (S ∩ I_Q') hSIQ'_bdd
    exact hN_eq
  have h_cover2 : ENat.toENNReal (dyadicCoveringNumber δ P1) =
      ENat.toENNReal (dyadicCoveringNumber δ P) := by
    have hP1_def : P1 = productLikeRealLineCopy (translateSet 1 S) := by rfl
    have hP_def : P = productLikeRealLineCopy S := by rfl
    rw [hP1_def, hP_def]
    have hN_eq : Nreal δ (translateSet 1 S) = Nreal δ S :=
      h_translate_Nreal S hS_bdd_real
    exact hN_eq
  have h_from_original := h_main hr hQ'_in hδr hr1
  rw [h_cover1, h_cover2]
  exact h_from_original

/-! ========================================================================
   Main ring expansion lemma
-/

/-- **Ring expansion on translated set A = B1 + 1 (corrected source order).**

Given B1 ⊆ [0,1] with delta-set and covering-number bounds, and the
**bad-direction measure** μ (normalized restriction of the original direction
measure to the bad set), let A := B1 + 1 ⊆ [1,2]. Apply `h_ring_spec`
to A and μ, returning A along with the expansion point x ∈ μ.support.

**Key interface points (operator correction 17:58):**
- μ is a DirectionFrostman measure on BAD DIRECTIONS, not a measure on B1.
- x ∈ μ.support is a BAD PROJECTION DIRECTION.
- This SAME x is used in Lemma 5.1 with the dense witness G_x ⊆ A × B2.
- Do NOT translate μ when translating B1.
- Do NOT assume μ.support ⊆ B1.

Since translation by 1 is δ-aligned, Nreal δ A = Nreal δ B1 exactly,
and the delta-set property transfers exactly. No factor loss. -/
lemma ring_expansion_A
    {δ s κ0 K_work εnc εgain : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
        ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ A →
        Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
        ∃ x ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x * b) A A))
    {B1 : Set ℝ}
    (hB1_sub : B1 ⊆ Set.Icc 0 1)
    (hB1_delta : IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) B1)
    (hN_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B1)
    (hN_upper : Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    {μ : Measure ℝ}
    (hμ_frost : IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ) :
    ∃ (A : Set ℝ) (x : ℝ),
      A = translateSet 1 B1 ∧
      A ⊆ Set.Icc 1 2 ∧
      x ∈ μ.support ∧
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
        Nreal δ (Set.image2 (fun a b => a + x * b) A A) := by
  let A : Set ℝ := translateSet 1 B1
  have hA_sub : A ⊆ Set.Icc 1 2 := by
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    have h_b_in : b ∈ Set.Icc 0 1 := hB1_sub hb
    have h0 : 0 ≤ b := h_b_in.1
    have h1 : b ≤ 1 := h_b_in.2
    exact ⟨by linarith, by linarith⟩
  have hA_delta : IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A :=
    delta_set_add_one hδ_dyadic hB1_delta
  have hB1_bdd : IsBounded B1 := by
    have h : IsBounded (productLikeRealLineCopy B1) := hB1_delta.1
    have h_proj_lip : LipschitzWith 1 (fun (x : EuclideanSpace ℝ (Fin 1)) => x 0) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp [EuclideanSpace.dist_eq, Fin.sum_univ_one] <;> exact le_refl _
    have hS_eq : B1 = (fun (x : EuclideanSpace ℝ (Fin 1)) => x 0) '' productLikeRealLineCopy B1 := by
      ext y
      simp only [productLikeRealLineCopy, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro h
        let pt : ℝ → EuclideanSpace ℝ (Fin 1) := fun y => (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
        exact ⟨pt y, h, by simp [pt]⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    rw [hS_eq]
    exact h_proj_lip.isBounded_image h
  have hN_A_eq : Nreal δ A = Nreal δ B1 := by
    rcases dyadic_one_is_delta_mul_int hδ_dyadic with ⟨m, hm⟩
    exact nreal_translation_by_delta_int hδ_pos hB1_bdd hm
  have hN_lower_A : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ A := by
    rw [hN_A_eq]; exact hN_lower
  have hN_upper_A : Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    rw [hN_A_eq]; exact hN_upper
  rcases h_ring_spec A μ hA_sub hA_delta hN_lower_A hN_upper_A hμ_frost with ⟨x, hx, h_exp⟩
  exact ⟨A, x, rfl, hA_sub, hx, h_exp⟩

/-! ========================================================================
   Lemma 5.1 wrapper — lower projection bound with constant factor
-/

/-- **Lemma 5.1 lower projection bound at the bad direction (corrected source order).**

Given additive expansion of A at the bad direction x (from ring_expansion_A),
controlled difference sets, and a dense graph G_x ⊆ A × B2, apply
`discretized_lemma51` to obtain:

  N(π_x(G_x)) ≥ (c_proj / (16·K_BSG²)) · δ^{-εgain} · N(B2)

**Same-direction contradiction (operator correction 17:58):**
- x is the SAME bad direction from ring_expansion_A.
- G_x is the dense witness with SMALL π_x(G_x) from the bad-direction property.
- Lemma 5.1 gives a LOWER bound on π_x(G_x) from the additive expansion.
- The bad-direction property gives an UPPER bound on π_x(G_x).
- These contradict when εgain > L·η.

**Compatibility with lossful projection bound (operator correction 17:42):**
Upper bound: N(π_x(G_x)) ≤ δ^{-Lη} · N(Pbar)^{1/2}.
Since B2 retains c_retention of Pbar's projection:
  N(B2) ≥ c_retention · N(Pbar)^{1/2}
Therefore lower bound ≥ C'_const · δ^{-εgain} · N(Pbar)^{1/2}.
Contradiction requires εgain > L·η. -/
lemma lemma51_lower_projection_bound_corrected
    {δ s x εgain c_proj K_BSG : ℝ} (hδ_pos : 0 < δ) (hx_abs : |x| ≤ 1)
    {B1 B2 : Set ℝ}
    (hB1_bdd : IsBounded B1) (hB2_bdd : IsBounded B2)
    {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG_bdd : IsBounded G)
    (hG_sub : ∀ p ∈ G, p 0 ∈ B1 ∧ p 1 ∈ B2)
    (hG_dense : ENat.toENNReal (dyadicCoveringNumber δ G) ≥
      ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2)
    (h_expansion : ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B1 ≤
      Nreal δ (Set.image2 (fun a b => a + x * b) B1 B1))
    (h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤
      ENNReal.ofReal K_BSG * Nreal δ B1)
    (h_diff2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
      ENNReal.ofReal K_BSG * Nreal δ B1)
    (hN_B1_pos : 0 < Nreal δ B1)
    (hN_B1_ne_top : Nreal δ B1 ≠ ⊤)
    (hc_proj_pos : 0 < c_proj) (hK_BSG_pos : 0 < K_BSG)
    (hεgain_pos : 0 < εgain) :
    ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2 ≤
    ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) := by
  set N_B1 : ENNReal := Nreal δ B1 with hN_B1
  set N_B2 : ENNReal := Nreal δ B2 with hN_B2
  set N_exp : ENNReal := Nreal δ (Set.image2 (fun a b => a + x * b) B1 B1) with hN_exp
  set N_D1 : ENNReal := Nreal δ (Set.image2 (· - ·) B1 B1) with hN_D1
  set N_D2 : ENNReal := Nreal δ (Set.image2 (· - ·) B2 B1) with hN_D2
  set N_G : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ G) with hN_G
  set N_proj : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) with hN_proj
  set c : ENNReal := ENNReal.ofReal c_proj with hc
  set K : ENNReal := ENNReal.ofReal K_BSG with hK
  set E : ENNReal := ENNReal.ofReal (δ ^ (-εgain)) with hE
  set C16 : ENNReal := ENNReal.ofReal (16 * K_BSG^2) with hC16

  have hN_B1_ne_zero : N_B1 ≠ 0 := ne_of_gt hN_B1_pos
  have hN_B1_sq_ne_zero : N_B1 * N_B1 ≠ 0 := mul_ne_zero hN_B1_ne_zero hN_B1_ne_zero
  have hN_B1_sq_ne_top : N_B1 * N_B1 ≠ ⊤ := mul_ne_top hN_B1_ne_top hN_B1_ne_top

  have hK_BSG_sq_pos : 0 < 16 * K_BSG^2 := by positivity
  have hC16_ne_zero : C16 ≠ 0 := by
    rw [hC16]
    exact ENNReal.ofReal_ne_zero_iff.mpr hK_BSG_sq_pos
  have hC16_ne_top : C16 ≠ ⊤ := by
    rw [hC16]
    exact ENNReal.ofReal_ne_top

  have h_C16_eq : C16 = 16 * K * K := by
    rw [hC16, hK]
    have h_pos : 0 ≤ K_BSG := by linarith
    have h1 : ENNReal.ofReal (16 * K_BSG^2) =
        ENNReal.ofReal (16 : ℝ) * ENNReal.ofReal (K_BSG^2) := by
      exact ENNReal.ofReal_mul (show (0 : ℝ) ≤ 16 by norm_num)
    have h2 : ENNReal.ofReal (K_BSG^2) =
        ENNReal.ofReal K_BSG * ENNReal.ofReal K_BSG := by
      have h21 : K_BSG^2 = K_BSG * K_BSG := by ring
      rw [h21]
      exact ENNReal.ofReal_mul h_pos
    have h3 : ENNReal.ofReal (16 : ℝ) = (16 : ENNReal) := by
      exact ofReal_ofNat 16
    rw [h1, h2, h3]
    <;> ring

  have h_main : N_exp * N_G ≤ 16 * N_D1 * N_D2 * N_proj :=
    WeakTwoEndsSumProduct.discretized_lemma51 hδ_pos hx_abs hB1_bdd hB2_bdd hG_bdd hG_sub

  have h1 : (E * N_B1) * (c * N_B1 * N_B2) ≤ N_exp * N_G :=
    mul_le_mul h_expansion hG_dense (by positivity) (by positivity)

  have h1' : E * c * (N_B1 * N_B1) * N_B2 ≤ N_exp * N_G := by
    have h_eq : (E * N_B1) * (c * N_B1 * N_B2) = E * c * (N_B1 * N_B1) * N_B2 := by ring
    rw [h_eq] at h1
    exact h1

  have h2 : 16 * N_D1 * N_D2 * N_proj ≤ C16 * (N_B1 * N_B1) * N_proj := by
    have h2a : N_D1 ≤ K * N_B1 := h_diff1
    have h2b : N_D2 ≤ K * N_B1 := h_diff2
    calc
      16 * N_D1 * N_D2 * N_proj
        ≤ 16 * (K * N_B1) * N_D2 * N_proj := by gcongr
      _ ≤ 16 * (K * N_B1) * (K * N_B1) * N_proj := by gcongr
      _ = C16 * (N_B1 * N_B1) * N_proj := by
        rw [h_C16_eq] <;> ring

  have h3 : E * c * (N_B1 * N_B1) * N_B2 ≤ C16 * (N_B1 * N_B1) * N_proj :=
    le_trans h1' (le_trans h_main h2)

  have h3' : (N_B1 * N_B1) * (E * c * N_B2) ≤ (N_B1 * N_B1) * (C16 * N_proj) := by
    have h_eq1 : (N_B1 * N_B1) * (E * c * N_B2) = E * c * (N_B1 * N_B1) * N_B2 := by ring
    have h_eq2 : (N_B1 * N_B1) * (C16 * N_proj) = C16 * (N_B1 * N_B1) * N_proj := by ring
    rw [h_eq1, h_eq2]
    exact h3

  have h4 : E * c * N_B2 ≤ C16 * N_proj := by
    have h_iff : (N_B1 * N_B1) * (E * c * N_B2) ≤ (N_B1 * N_B1) * (C16 * N_proj) ↔
        E * c * N_B2 ≤ C16 * N_proj :=
      ENNReal.mul_le_mul_iff_right hN_B1_sq_ne_zero hN_B1_sq_ne_top
    exact h_iff.mp h3'

  have h_div : C16⁻¹ * c = ENNReal.ofReal (c_proj / (16 * K_BSG^2)) := by
    have h_pos1 : 0 < 16 * K_BSG^2 := hK_BSG_sq_pos
    have h_nonneg2 : 0 ≤ c_proj := by linarith
    have h1 : C16⁻¹ = ENNReal.ofReal ((16 * K_BSG^2)⁻¹) := by
      rw [hC16]
      exact (ENNReal.ofReal_inv_of_pos h_pos1).symm
    calc
      C16⁻¹ * c
        = ENNReal.ofReal ((16 * K_BSG^2)⁻¹) * ENNReal.ofReal c_proj := by rw [h1, hc]
      _ = ENNReal.ofReal (((16 * K_BSG^2)⁻¹) * c_proj) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        <;> rfl
      _ = ENNReal.ofReal (c_proj / (16 * K_BSG^2)) := by
        congr 1
        field_simp [h_pos1.ne'] <;> ring

  have h_rhs : C16⁻¹ * (C16 * N_proj) = N_proj := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hC16_ne_zero hC16_ne_top, one_mul]

  have h_lhs : C16⁻¹ * (E * c * N_B2) =
      ENNReal.ofReal (c_proj / (16 * K_BSG^2)) * E * N_B2 := by
    calc
      C16⁻¹ * (E * c * N_B2)
        = C16⁻¹ * c * E * N_B2 := by ring
      _ = ENNReal.ofReal (c_proj / (16 * K_BSG^2)) * E * N_B2 := by rw [h_div]

  calc
    ENNReal.ofReal (c_proj / (16 * K_BSG^2)) * E * N_B2
      = C16⁻¹ * (E * c * N_B2) := by rw [h_lhs]
    _ ≤ C16⁻¹ * (C16 * N_proj) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = N_proj := by rw [h_rhs]

/-! ========================================================================
   Polynomial-loss corollary
-/

/-- **Lemma 5.1 lower bound with explicit polynomial loss.**

Thin wrapper around `lemma51_lower_projection_bound_corrected` that takes
a single loss exponent `C_loss` instead of separate constants `c_proj` and `K_BSG`.

When the graph density is `δ^{C_loss}` and difference-set blowup is `δ^{-C_loss}`,
the combined loss is `δ^{3·C_loss}`, giving:

```
N(π_x(G)) ≥ (1/16) · δ^{-εgain + 3·C_loss} · N(B2)
```

This exposes the polynomial loss explicitly so the final exponent comparison
`εgain > L·η + 4·C_loss` can be made after applying the `N(B2)` lower bound.

**Coordinate order (operator correction Section 5):**
- `hG_sub`: `p 0 ∈ B1`, `p 1 ∈ B2`
- Ring applied to `B1+1`, Lemma 5.1 at same direction `x`
- Matches `discretized_lemma51` with `A := B1`, `B := B2` -/
lemma lemma51_polynomial_loss
    {δ s x εgain C_loss : ℝ} (hδ_pos : 0 < δ) (hx_abs : |x| ≤ 1)
    {B1 B2 : Set ℝ}
    (hB1_bdd : IsBounded B1) (hB2_bdd : IsBounded B2)
    {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG_bdd : IsBounded G)
    (hG_sub : ∀ p ∈ G, p 0 ∈ B1 ∧ p 1 ∈ B2)
    (hG_dense : ENat.toENNReal (dyadicCoveringNumber δ G) ≥
      ENNReal.ofReal (δ ^ C_loss) * Nreal δ B1 * Nreal δ B2)
    (h_expansion : ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B1 ≤
      Nreal δ (Set.image2 (fun a b => a + x * b) B1 B1))
    (h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤
      ENNReal.ofReal (δ ^ (-C_loss)) * Nreal δ B1)
    (h_diff2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
      ENNReal.ofReal (δ ^ (-C_loss)) * Nreal δ B1)
    (hN_B1_pos : 0 < Nreal δ B1)
    (hN_B1_ne_top : Nreal δ B1 ≠ ⊤)
    (hεgain_pos : 0 < εgain) :
    (1 / 16 : ENNReal) * ENNReal.ofReal (δ ^ (-εgain + 3 * C_loss)) * Nreal δ B2 ≤
    ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) := by
  set c_proj : ℝ := δ ^ C_loss with hc_proj_def
  set K_BSG : ℝ := δ ^ (-C_loss) with hK_BSG_def
  have h_c_proj_pos : 0 < c_proj := by
    rw [hc_proj_def]
    positivity
  have h_K_BSG_pos : 0 < K_BSG := by
    rw [hK_BSG_def]
    positivity
  have h_main := lemma51_lower_projection_bound_corrected (s := s)
    (hδ_pos := hδ_pos) (hx_abs := hx_abs)
    (hB1_bdd := hB1_bdd) (hB2_bdd := hB2_bdd)
    (hG_bdd := hG_bdd) (hG_sub := hG_sub)
    (hG_dense := hG_dense) (h_expansion := h_expansion)
    (h_diff1 := h_diff1) (h_diff2 := h_diff2)
    (hN_B1_pos := hN_B1_pos) (hN_B1_ne_top := hN_B1_ne_top)
    (hc_proj_pos := h_c_proj_pos) (hK_BSG_pos := h_K_BSG_pos)
    (hεgain_pos := hεgain_pos)
  have h_pos : 0 < δ := hδ_pos
  have h_real : (c_proj / (16 * K_BSG^2)) * δ ^ (-εgain) =
      (1 / 16 : ℝ) * δ ^ (-εgain + 3 * C_loss) := by
    rw [hc_proj_def, hK_BSG_def]
    have h1 : (δ ^ (-C_loss)) ^ 2 = δ ^ (-C_loss) * δ ^ (-C_loss) := by
      simp [pow_two]
    have h2 : δ ^ (-C_loss) * δ ^ (-C_loss) = δ ^ (-2 * C_loss) := by
      rw [← Real.rpow_add h_pos] <;> ring_nf
    have h2' : (δ ^ (-C_loss)) ^ 2 = δ ^ (-2 * C_loss) := by
      rw [h1, h2]
    have h3 : (δ ^ (-2 * C_loss))⁻¹ = δ ^ (2 * C_loss) := by
      have h31 : δ ^ (-2 * C_loss) = (δ ^ (2 * C_loss))⁻¹ := by
        have h32 : (-2 * C_loss) = -(2 * C_loss) := by ring
        rw [h32]
        rw [Real.rpow_neg h_pos.le]
      rw [h31]
      have h_ne_zero : δ ^ (2 * C_loss) ≠ 0 := by positivity
      exact InvolutiveInv.inv_inv (δ ^ (2 * C_loss))
    calc
      (δ ^ C_loss / (16 * (δ ^ (-C_loss)) ^ 2)) * δ ^ (-εgain)
        = (δ ^ C_loss / (16 * δ ^ (-2 * C_loss))) * δ ^ (-εgain) := by rw [h2']
      _ = ((1 / 16 : ℝ) * δ ^ C_loss * (δ ^ (-2 * C_loss))⁻¹) * δ ^ (-εgain) := by
        have h4 : δ ^ C_loss / (16 * δ ^ (-2 * C_loss)) =
            (1 / 16 : ℝ) * δ ^ C_loss * (δ ^ (-2 * C_loss))⁻¹ := by
          have h5 : δ ^ (-2 * C_loss) ≠ 0 := by positivity
          field_simp [h5] <;> ring
        rw [h4]
      _ = ((1 / 16 : ℝ) * δ ^ C_loss * δ ^ (2 * C_loss)) * δ ^ (-εgain) := by rw [h3]
      _ = (1 / 16 : ℝ) * (δ ^ C_loss * δ ^ (2 * C_loss)) * δ ^ (-εgain) := by ring
      _ = (1 / 16 : ℝ) * δ ^ (3 * C_loss) * δ ^ (-εgain) := by
        have h6 : δ ^ C_loss * δ ^ (2 * C_loss) = δ ^ (3 * C_loss) := by
          rw [← Real.rpow_add h_pos] <;> ring_nf
        rw [h6] <;> ring
      _ = (1 / 16 : ℝ) * δ ^ (-εgain + 3 * C_loss) := by
        have h7 : δ ^ (3 * C_loss) * δ ^ (-εgain) = δ ^ (-εgain + 3 * C_loss) := by
          rw [← Real.rpow_add h_pos] <;> ring_nf
        have h8 : (1 / 16 : ℝ) * δ ^ (3 * C_loss) * δ ^ (-εgain) =
            (1 / 16 : ℝ) * (δ ^ (3 * C_loss) * δ ^ (-εgain)) := by ring
        rw [h8, h7]
  have h_simplify : ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) =
    (1 / 16 : ENNReal) * ENNReal.ofReal (δ ^ (-εgain + 3 * C_loss)) := by
    have h_left : ENNReal.ofReal (c_proj / (16 * K_BSG^2)) * ENNReal.ofReal (δ ^ (-εgain)) =
        ENNReal.ofReal ((c_proj / (16 * K_BSG^2)) * δ ^ (-εgain)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
    have h_right : ENNReal.ofReal ((1 / 16 : ℝ) * δ ^ (-εgain + 3 * C_loss)) =
        (1 / 16 : ENNReal) * ENNReal.ofReal (δ ^ (-εgain + 3 * C_loss)) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / 16 by norm_num)]
      <;> simp
    rw [h_left, h_real, h_right]
  rw [h_simplify] at h_main
  exact h_main

end ProductLikeIncidence.ProductReduction
