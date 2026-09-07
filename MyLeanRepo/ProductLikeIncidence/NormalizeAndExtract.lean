module

/-
# Normalize and Extract Wrapper

Normalizes a bounded E3' to [0,1]^2 via power-of-2 affine scaling,
calls `extract_A1_A2_bridge`, then denormalizes the outputs.

## Key design

- Original scale δ is dyadic and ≤ 1
- Normalized scale δ' = δ/L remains dyadic (divide by power of 2)
- T(p) = ((p0+R)/L, (p1+R)/L) where L = 2^k, R = L/2 = 2^{k-1}
- Since R is a positive integer, denormalization translation by -R preserves δ-sets
  exactly (integer is multiple of every dyadic r≤1)
- Scaling by L maps δ'-sets to δ=L·δ'-sets

## Main lemma
`normalize_and_extract` — full normalization-bridge-denormalization pipeline

## Whiteprint node
`normalize_and_extract`
-/

public import MyLeanRepo.ProductLikeIncidence.CoordinateNormalization
public import MyLeanRepo.ProductLikeIncidence.RoundingExtractionBridge
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ### Helper: scaling real sets and intervals -/

/-- Scaling a set then intersecting with an interval equals
scaling the intersection with the scaled interval. -/
lemma scaleSet_inter_Ico {L : ℝ} (hL : 0 < L) {A : Set ℝ} {a b : ℝ} :
    scaleSet L A ∩ Set.Ico a b =
    scaleSet L (A ∩ Set.Ico (a / L) (b / L)) := by
  ext y
  simp only [scaleSet, Set.mem_image, Set.mem_inter_iff, Set.mem_Ico]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ha, hb⟩
    have h1 : a / L ≤ x := by
      calc a / L ≤ (L * x) / L := by gcongr
           _ = x := by field_simp [hL.ne'] <;> ring
    have h2 : x < b / L := by
      calc x = (L * x) / L := by field_simp [hL.ne'] <;> ring
           _ < b / L := by gcongr
    exact ⟨x, ⟨hx, h1, h2⟩, rfl⟩
  · rintro ⟨x, ⟨hx, ha, hb⟩, rfl⟩
    have h1 : a ≤ L * x := by
      calc a = (a / L) * L := by field_simp [hL.ne'] <;> ring
           _ ≤ x * L := by gcongr
           _ = L * x := by ring
    have h2 : L * x < b := by
      calc L * x = x * L := by ring
               _ < (b / L) * L := by gcongr
               _ = b := by field_simp [hL.ne'] <;> ring
    exact ⟨⟨x, hx, rfl⟩, h1, h2⟩

/-- Intersecting `realLineCopy A` with a 1D dyadic cube equals
`realLineCopy (A ∩ corresponding interval)`. -/
lemma realLineCopy_inter_dyadicCube {r : ℝ} {A : Set ℝ} {k : Fin 1 → ℤ} :
    productLikeRealLineCopy A ∩ dyadicCube r k =
    productLikeRealLineCopy (A ∩ Set.Ico (r * (k 0 : ℝ)) (r * ((k 0 : ℝ) + 1))) := by
  ext x
  simp only [productLikeRealLineCopy, dyadicCube, Set.mem_inter_iff,
    Set.mem_setOf_eq, Set.mem_Ico]
  have h_all : (∀ (i : Fin 1), r * (k i : ℝ) ≤ x i ∧ x i < r * ((k i : ℝ) + 1)) ↔
      r * (k 0 : ℝ) ≤ x 0 ∧ x 0 < r * ((k 0 : ℝ) + 1) := by
    constructor
    · intro h; exact h 0
    · intro h i; fin_cases i; exact h
  rw [h_all]
  <;> aesop

/-! ### Helper: scaling of δ-sets -/

/-- `realLineCopy` and `productLikeRealLineCopy` are equal by definition. -/
lemma realLineCopy_eq_productLike (A : Set ℝ) :
    realLineCopy A = productLikeRealLineCopy A := by
  ext x
  simp [realLineCopy, productLikeRealLineCopy]

/-- Convert `Nreal` to covering number with `productLikeRealLineCopy`. -/
lemma Nreal_to_productLike (δ : ℝ) (A : Set ℝ) :
    Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by
  have h_eq : realLineCopy A = productLikeRealLineCopy A := realLineCopy_eq_productLike A
  simp [Nreal, h_eq]

/-- If A is a `(δ', s, C)`-set and L = 2^k, then `scaleSet L A` is a
`(L*δ', s, C)`-set, provided `L*δ'` is a dyadic scale ≤ 1.

Proof: scaling by L maps (r/L)-cubes to r-cubes bijectively.
Covering numbers satisfy `N(Lδ', L·A ∩ Q) = N(δ', A ∩ Q/L)`.
Apply the δ-set bound at scale r/L, then use `(r/L)^s ≤ r^s`. -/
lemma deltaSCSet_scale_up {δ' s C : ℝ} {A : Set ℝ}
    (hδ'_pos : 0 < δ') (hδ'_dyadic : δ' ∈ dyadicScales)
    (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C)
    (L : ℝ) (k : ℕ) (hL : L = (2 : ℝ) ^ k)
    (hδ_scaled_dyadic : (L * δ') ∈ dyadicScales)
    (hδ_scaled_le_one : L * δ' ≤ 1)
    (hA_bdd : Bornology.IsBounded A)
    (h : IsProductLikeRealDeltaSCSet δ' s C A) :
    IsProductLikeRealDeltaSCSet (L * δ') s C (scaleSet L A) := by
  rcases h with ⟨h_bdd, h_nonempty, _, _, _, hs_nonneg', hs_le_one', hC_pos', h_main⟩
  have hL_pos : 0 < L := by
    rw [hL]; positivity
  have hL_one : 1 ≤ L := by
    rw [hL]
    have h : 1 ≤ (2 : ℕ) ^ k := by
      exact Nat.one_le_two_pow
    exact_mod_cast h
  have hδ_scaled_pos : 0 < L * δ' := mul_pos hL_pos hδ'_pos
  set δ := L * δ' with hδ_def

  -- Boundedness of scaled set
  have h1 : Bornology.IsBounded (scaleSet L A) :=
    WeakTwoEndsSumProduct.scaleSet_bounded hA_bdd
  have h_scaled_bdd : Bornology.IsBounded (productLikeRealLineCopy (scaleSet L A)) :=
    productLikeRealLineCopy_bounded h1
  -- Nonempty
  have h_scaled_nonempty : (productLikeRealLineCopy (scaleSet L A)).Nonempty := by
    have h1 : (scaleSet L A).Nonempty := by
      rcases h_nonempty with ⟨x, hx⟩
      exact ⟨L * (x 0), x 0, hx, by ring⟩
    rcases h1 with ⟨z, hz⟩
    let p : EuclideanSpace ℝ (Fin 1) :=
      (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun (_ : Fin 1) => z)
    have hp0 : p 0 = z := by
      change ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun (_ : Fin 1) => z)) 0 = z
      simp
    exact ⟨p, by simp [productLikeRealLineCopy, hp0] <;> exact hz⟩

  -- Main bound
  have h_main' : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 1))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A) ∩ Q)) ≤
      ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A))) *
        ENNReal.ofReal (r ^ s) := by
    intro r Q hr_dyadic hQ hδ_le_r hr_le_one
    rcases hQ with ⟨k_idx, rfl⟩
    let k0 : ℤ := k_idx 0
    let a := r * (k0 : ℝ)
    let b := r * ((k0 : ℝ) + 1)
    let a' := (r / L) * (k0 : ℝ)
    let b' := (r / L) * ((k0 : ℝ) + 1)

    -- r/L is dyadic
    have hrL_dyadic : (r / L) ∈ dyadicScales := by
      have h1 : r / L = r / (2 : ℝ) ^ k := by rw [hL]
      rw [h1]
      exact dyadicScale_div_pow2 hr_dyadic
    -- r/L ≥ δ'
    have hrL_ge_δ' : δ' ≤ r / L := by
      have h : L * δ' ≤ r := by
        have h' : δ ≤ r := hδ_le_r
        simpa [hδ_def] using h'
      calc δ' = (L * δ') / L := by field_simp [hL_pos.ne'] <;> ring
           _ ≤ r / L := by gcongr
    -- r/L ≤ 1
    have hrL_le_one : r / L ≤ 1 := by
      rw [div_le_one hL_pos] <;> linarith

    -- Step 1: realLineCopy (scaleSet L A) ∩ cube = realLineCopy (scaleSet L A ∩ Ico a b)
    have h1 : productLikeRealLineCopy (scaleSet L A) ∩ dyadicCube r k_idx =
        productLikeRealLineCopy (scaleSet L A ∩ Set.Ico a b) :=
      realLineCopy_inter_dyadicCube

    -- Step 2: scaleSet L A ∩ Ico a b = scaleSet L (A ∩ Ico a' b')
    have ha' : a' = a / L := by
      simp [a, a', mul_comm] <;> ring
    have hb' : b' = b / L := by
      simp [b, b', mul_comm] <;> ring
    have h2 : scaleSet L A ∩ Set.Ico a b = scaleSet L (A ∩ Set.Ico a' b') := by
      rw [ha', hb']
      exact scaleSet_inter_Ico hL_pos

    have hδ_div_L_eq : δ / L = δ' := by
      rw [hδ_def] <;> field_simp [hL_pos.ne'] <;> ring

    -- Step 3: Nreal δ (scaleSet L A ∩ Ico a b) = Nreal δ' (A ∩ Ico a' b')
    have hA_inter_bdd : Bornology.IsBounded (A ∩ Set.Ico a' b') :=
      hA_bdd.subset (by simp)
    have h3 : Nreal δ (scaleSet L A ∩ Set.Ico a b) = Nreal δ' (A ∩ Set.Ico a' b') := by
      rw [h2]
      have h_scaling := WeakTwoEndsSumProduct.Nreal_scaling hδ_scaled_pos hL_pos hA_inter_bdd
      rw [hδ_div_L_eq] at h_scaling
      exact h_scaling

    -- Step 4: realLineCopy (A ∩ Ico a' b') = realLineCopy A ∩ dyadicCube (r/L) k_idx
    have h4 : productLikeRealLineCopy (A ∩ Set.Ico a' b') =
        productLikeRealLineCopy A ∩ dyadicCube (r / L) k_idx := by
      have h_tmp := realLineCopy_inter_dyadicCube (r := r / L) (A := A) (k := k_idx)
      have h_eq1 : Set.Ico ((r / L) * (k_idx 0 : ℝ)) ((r / L) * ((k_idx 0 : ℝ) + 1)) = Set.Ico a' b' := by
        congr <;> simp [a', b'] <;> ring
      rw [h_eq1] at h_tmp
      exact h_tmp.symm

    -- Step 5: apply h_main at scale r/L
    have h5 : ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy A ∩ dyadicCube (r / L) k_idx)) ≤
        ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy A)) *
          ENNReal.ofReal ((r / L) ^ s) :=
      h_main hrL_dyadic ⟨k_idx, rfl⟩ hrL_ge_δ' hrL_le_one

    -- Step 6: Nreal δ' A = Nreal δ (scaleSet L A)
    have h6 : Nreal δ' A = Nreal δ (scaleSet L A) := by
      have h_scaling := WeakTwoEndsSumProduct.Nreal_scaling hδ_scaled_pos hL_pos hA_bdd
      rw [hδ_div_L_eq] at h_scaling
      exact h_scaling.symm

    -- Conversions between Nreal (uses realLineCopy) and productLikeRealLineCopy
    have h_cnv1 : ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A) ∩ dyadicCube r k_idx)) =
        Nreal δ (scaleSet L A ∩ Set.Ico a b) := by
      rw [h1]
      exact (Nreal_to_productLike δ (scaleSet L A ∩ Set.Ico a b)).symm
    have h_cnv2 : Nreal δ' (A ∩ Set.Ico a' b') =
        ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy (A ∩ Set.Ico a' b'))) :=
      Nreal_to_productLike δ' (A ∩ Set.Ico a' b')
    have h_cnv3 : ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy A)) = Nreal δ' A :=
      (Nreal_to_productLike δ' A).symm
    have h_cnv4 : Nreal δ (scaleSet L A) =
        ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A))) :=
      Nreal_to_productLike δ (scaleSet L A)

    -- Power inequality
    have hr_pos : 0 < r := by
      rcases hr_dyadic with ⟨n, hn⟩
      rw [hn] <;> positivity
    have h_pow : (r / L) ^ s ≤ r ^ s := by
      have h1 : 0 ≤ r / L := by positivity
      have h2 : r / L ≤ r := by apply div_le_self <;> linarith
      exact Real.rpow_le_rpow h1 h2 hs_nonneg'
    have h_pow_enn : ENNReal.ofReal ((r / L) ^ s) ≤ ENNReal.ofReal (r ^ s) := by
      have h : (r / L) ^ s ≤ r ^ s := h_pow
      exact ofReal_le_ofReal h_pow


    calc
      ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A) ∩ dyadicCube r k_idx))
        = Nreal δ (scaleSet L A ∩ Set.Ico a b) := h_cnv1
      _ = Nreal δ' (A ∩ Set.Ico a' b') := h3
      _ = ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy (A ∩ Set.Ico a' b'))) := h_cnv2
      _ = ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy A ∩ dyadicCube (r / L) k_idx)) := by rw [h4]
      _ ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ' (productLikeRealLineCopy A)) *
            ENNReal.ofReal ((r / L) ^ s) := h5
      _ = ENNReal.ofReal C * Nreal δ' A * ENNReal.ofReal ((r / L) ^ s) := by
          rw [h_cnv3]
      _ = ENNReal.ofReal C * Nreal δ (scaleSet L A) * ENNReal.ofReal ((r / L) ^ s) := by rw [h6]
      _ ≤ ENNReal.ofReal C * Nreal δ (scaleSet L A) * ENNReal.ofReal (r ^ s) := by
          exact mul_le_mul_of_nonneg_left h_pow_enn (by positivity)
      _ = ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A))) *
            ENNReal.ofReal (r ^ s) := by
        have h_goal : ENNReal.ofReal C * Nreal δ (scaleSet L A) * ENNReal.ofReal (r ^ s) =
            ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet L A))) *
              ENNReal.ofReal (r ^ s) := by
          rw [h_cnv4]
          <;> ring
        exact h_goal

  exact ⟨h_scaled_bdd, h_scaled_nonempty, by norm_num, hδ_scaled_dyadic, hδ_scaled_pos,
    hs_nonneg', hs_le_one', hC_pos', h_main'⟩

/-! ### Energy bridge: original-scale to normalized-scale -/

/-- Convert an original-scale Riesz energy bound to a normalized-scale bound.

If `ν` is a 1D measure with energy bound at scale `δ`, and we normalize by
`normalizeMap R L` (which scales distances by `1/L`), then the normalized energy
at scale `δ/L` is `L^{2κ0}` times the original energy.

To absorb this factor into the bound, we need `2κ0 ≤ η_total` and `L ≥ 1`, giving
`L^{2κ0} * C_energy * δ^{-η_total} ≤ C_energy * (δ/L)^{-η_total}`.

This is the "energy bridge" `I_{δ'}(T_*ν) = L^{2κ0} · I_δ(ν)`. -/
lemma normalized_energy_bridge
    {δ κ0 η_total C_energy : ℝ} (hδ_pos : 0 < δ)
    (hkappa_pos : 0 < κ0) (hη_total_pos : 0 < η_total)
    (h2κ0_le_ηtotal : 2 * κ0 ≤ η_total)
    (R L : ℝ) (hR_pos : 0 < R) (hL : L = 2 * R) (hL_pos : 0 < L) (hL_ge_one : 1 ≤ L)
    (hC_pos : 0 < C_energy)
    {ν : Measure ℝ} [SFinite ν]
    (h_energy_orig : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos ν ≤
        ENNReal.ofReal (C_energy * δ ^ (-η_total))) :
    robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
      (Measure.map (normalizeMap R L) ν) ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total)) := by
  set c : ℝ := 1 / L with hc_def
  have hc_pos : 0 < c := by positivity
  have hcδ_eq : c * δ = δ / L := by
    rw [hc_def] <;> field_simp [hL_pos.ne'] <;> ring
  have hT_meas : Measurable (normalizeMap R L) := by
    have h_cont : Continuous (fun x : ℝ => (x + R) / L) := by continuity
    have h_eq : (normalizeMap R L) = (fun x : ℝ => (x + R) / L) := by
      funext x; simp [normalizeMap]
    rw [h_eq]; exact h_cont.measurable
  have hT_dist : ∀ (x y : ℝ), dist (normalizeMap R L x) (normalizeMap R L y) = c * dist x y := by
    intro x y
    rw [normalizeMap_dist hR_pos hL x y, hc_def] <;> ring
  let h_cδ_pos : 0 < c * δ := mul_pos hc_pos hδ_pos
  have h_scaling : robust_projection_main.rieszEnergy (2 * κ0) h_cδ_pos
      (Measure.map (normalizeMap R L) ν) =
      ENNReal.ofReal (c ^ (-(2 * κ0))) * robust_projection_main.rieszEnergy (2 * κ0) hδ_pos ν :=
    rieszEnergy_affine_scaling hδ_pos hc_pos (normalizeMap R L) hT_meas hT_dist ν
  have h_c_pow : c ^ (-(2 * κ0)) = L ^ (2 * κ0) := by
    rw [hc_def]
    have h_pos1 : 0 < (1 / L : ℝ) := by positivity
    have h : (1 / L : ℝ) ^ (-(2 * κ0)) = ((1 / L : ℝ) ^ (2 * κ0))⁻¹ := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    rw [h]
    have h2 : ((1 / L : ℝ) ^ (2 * κ0))⁻¹ = L ^ (2 * κ0) := by
      have h3 : (1 / L : ℝ) ^ (2 * κ0) = (L ^ (2 * κ0))⁻¹ := by
        have h4 : (1 / L : ℝ) = L⁻¹ := by field_simp
        rw [h4]
        exact Real.inv_rpow (by linarith) (2 * κ0)
      rw [h3] <;> field_simp
    exact h2
  have h_δL_pow : (δ / L) ^ (-η_total) = L ^ η_total * δ ^ (-η_total) := by
    have h_pos2 : 0 < (δ / L : ℝ) := by positivity
    have h5 : (δ / L : ℝ) ^ (-η_total) = ((δ / L : ℝ) ^ η_total)⁻¹ := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    rw [h5]
    have h6 : (δ / L : ℝ) ^ η_total = δ ^ η_total / L ^ η_total := by
      rw [Real.div_rpow (by positivity) (by positivity)] <;> ring
    rw [h6]
    have h7 : (δ ^ η_total / L ^ η_total)⁻¹ = L ^ η_total / δ ^ η_total := by
      field_simp
    rw [h7]
    have h8 : L ^ η_total / δ ^ η_total = L ^ η_total * (δ ^ η_total)⁻¹ := by ring
    rw [h8]
    have h9 : (δ ^ η_total)⁻¹ = δ ^ (-η_total) := by
      rw [← Real.rpow_neg (by positivity)] <;> ring
    rw [h9] <;> ring
  have h_L_pow_le : L ^ (2 * κ0) ≤ L ^ η_total := by
    have h10 : 0 ≤ 2 * κ0 := by linarith
    gcongr
    <;> linarith
  have h_final : (L ^ (2 * κ0)) * (C_energy * δ ^ (-η_total)) ≤ C_energy * (δ / L) ^ (-η_total) := by
    rw [h_δL_pow]
    have h13 : C_energy * (L ^ η_total * δ ^ (-η_total)) = L ^ η_total * (C_energy * δ ^ (-η_total)) := by ring
    rw [h13]
    gcongr
    <;> linarith
  have h_main2 : ENNReal.ofReal ((L ^ (2 * κ0)) * (C_energy * δ ^ (-η_total))) ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total)) :=
    ENNReal.ofReal_le_ofReal h_final
  have h_scaling2 : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
      (Measure.map (normalizeMap R L) ν) =
      ENNReal.ofReal (L ^ (2 * κ0)) * robust_projection_main.rieszEnergy (2 * κ0) hδ_pos ν := by
    let P : ℝ → Prop := fun x =>
      ∀ (hx : 0 < x), robust_projection_main.rieszEnergy (2 * κ0) hx (Measure.map (normalizeMap R L) ν) =
        ENNReal.ofReal (c ^ (-(2 * κ0))) * robust_projection_main.rieszEnergy (2 * κ0) hδ_pos ν
    have hP_cδ : P (c * δ) := by
      intro hx
      exact h_scaling
    have hP_δL : P (δ / L) := hcδ_eq ▸ hP_cδ
    have h_step2 := hP_δL (div_pos hδ_pos hL_pos)
    rw [h_step2, h_c_pow]
  rw [h_scaling2]
  have h_mul : ENNReal.ofReal (L ^ (2 * κ0)) * robust_projection_main.rieszEnergy (2 * κ0) hδ_pos ν ≤
      ENNReal.ofReal (L ^ (2 * κ0)) * ENNReal.ofReal (C_energy * δ ^ (-η_total)) :=
    mul_le_mul_of_nonneg_left h_energy_orig (by positivity)
  have h_mul2 : ENNReal.ofReal (L ^ (2 * κ0)) * ENNReal.ofReal (C_energy * δ ^ (-η_total)) =
      ENNReal.ofReal ((L ^ (2 * κ0)) * (C_energy * δ ^ (-η_total))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    <;> ring
  rw [h_mul2] at h_mul
  exact le_trans h_mul h_main2

/-- qBox-cost energy bridge: if `I_δ(μ) ≤ δ^{-q}` and `L ≤ δ^{-qBox}`,
then `I_{δ/L}(map((x+R)/L, μ)) ≤ δ^{-(q + 2κ0·qBox)}`. -/
lemma normalized_coordinate_energy_bridge
    {δ L R κ0 q qBox : ℝ}
    (hδ_pos : 0 < δ) (hL_pos : 0 < L) (hR : 0 ≤ R)
    (hκ0_pos : 0 < κ0)
    {μ : Measure ℝ} [SFinite μ]
    (h_energy : robust_projection_main.rieszEnergy (2*κ0) hδ_pos μ ≤
        ENNReal.ofReal (δ ^ (-q)))
    (hL_bound : L ≤ δ ^ (-qBox)) :
    robust_projection_main.rieszEnergy (2*κ0) (div_pos hδ_pos hL_pos)
        (Measure.map (fun x : ℝ => (x + R) / L) μ) ≤
      ENNReal.ofReal (δ ^ (-(q + 2*κ0*qBox))) := by
  let T : ℝ → ℝ := fun x => (x + R) / L
  have hT_dist : ∀ (x y : ℝ), dist (T x) (T y) = (1/L) * dist x y := by
    intro x y; simp only [T, dist_eq_norm]
    have h2 : (x + R) / L - (y + R) / L = (x - y) / L := by ring
    rw [h2]
    have h3 : |(x - y) / L| = (1 / L) * |x - y| := by
      calc |(x - y) / L| = |x - y| / |L| := by rw [abs_div]
        _ = |x - y| / L := by rw [abs_of_pos hL_pos]
        _ = (1 / L) * |x - y| := by field_simp [hL_pos.ne']
    exact h3
  have hc_pos : 0 < (1/L) := by positivity
  have hT_meas : Measurable T := by
    have h_cont : Continuous T := by continuity
    exact h_cont.measurable
  let h_cδ_pos : 0 < (1/L)*δ := mul_pos hc_pos hδ_pos
  have h_scaling : robust_projection_main.rieszEnergy (2*κ0) h_cδ_pos (Measure.map T μ) =
      ENNReal.ofReal ((1/L)^(-(2*κ0))) * robust_projection_main.rieszEnergy (2*κ0) hδ_pos μ :=
    rieszEnergy_affine_scaling hδ_pos hc_pos T hT_meas hT_dist μ
  have h_nonneg : 0 ≤ L := by linarith
  have h_c_power : (1/L)^(-(2*κ0)) = L^(2*κ0) := by
    have h1 : (1/L)^(-(2*κ0)) = (L^(-(2*κ0)))⁻¹ := by
      have h11 : (1/L) = L⁻¹ := by field_simp
      rw [h11]
      exact Real.inv_rpow h_nonneg (-(2*κ0))
    rw [h1]
    have h2 : L^(-(2*κ0)) = (L^(2*κ0))⁻¹ := by
      rw [Real.rpow_neg h_nonneg]
    rw [h2]
    have h4 : L^(2*κ0) ≠ 0 := by positivity
    field_simp [h4]
  have h_energy2 : ENNReal.ofReal ((1/L)^(-(2*κ0))) * robust_projection_main.rieszEnergy (2*κ0) hδ_pos μ ≤
      ENNReal.ofReal (L^(2*κ0)) * ENNReal.ofReal (δ^(-q)) := by rw [h_c_power]; gcongr
  have h6 : ENNReal.ofReal (L^(2*κ0) * δ^(-q)) =
      ENNReal.ofReal (L^(2*κ0)) * ENNReal.ofReal (δ^(-q)) :=
    ENNReal.ofReal_mul (show 0 ≤ L^(2*κ0) from by positivity)
  have hL_pow_bound : L^(2*κ0) ≤ (δ^(-qBox))^(2*κ0) := Real.rpow_le_rpow h_nonneg hL_bound (by linarith)
  have h3 : (δ^(-qBox))^(2*κ0) = δ^(-qBox * (2*κ0)) := by rw [← Real.rpow_mul (by positivity)]
  have h4 : L^(2*κ0) ≤ δ^(-qBox * (2*κ0)) := by rw [h3] at hL_pow_bound; exact hL_pow_bound
  have h5 : -qBox * (2*κ0) = -(2*κ0*qBox) := by ring
  rw [h5] at h4
  have h7 : L^(2*κ0) * δ^(-q) ≤ δ^(-(2*κ0*qBox)) * δ^(-q) := by
    have h_pos : 0 ≤ δ^(-q) := by positivity
    exact mul_le_mul_of_nonneg_right h4 h_pos
  have h8 : δ^(-(2*κ0*qBox)) * δ^(-q) = δ^(-(q + 2*κ0*qBox)) := by rw [← Real.rpow_add (by positivity)] <;> ring_nf
  have h9 : ENNReal.ofReal (L^(2*κ0) * δ^(-q)) ≤ ENNReal.ofReal (δ ^ (-(q + 2*κ0*qBox))) := by
    rw [h8] at h7; exact ENNReal.ofReal_le_ofReal h7
  have h_eq1 : (1/L)*δ = δ/L := by field_simp [hL_pos.ne'] <;> ring
  have h_scaling2 : robust_projection_main.rieszEnergy (2*κ0) (div_pos hδ_pos hL_pos) (Measure.map T μ) =
      ENNReal.ofReal ((1/L)^(-(2*κ0))) * robust_projection_main.rieszEnergy (2*κ0) hδ_pos μ := by
    convert h_scaling using 2; · exact h_eq1.symm
  calc
    robust_projection_main.rieszEnergy (2*κ0) (div_pos hδ_pos hL_pos) (Measure.map T μ)
      = ENNReal.ofReal ((1/L)^(-(2*κ0))) * robust_projection_main.rieszEnergy (2*κ0) hδ_pos μ := h_scaling2
    _ ≤ ENNReal.ofReal (L^(2*κ0)) * ENNReal.ofReal (δ^(-q)) := h_energy2
    _ = ENNReal.ofReal (L^(2*κ0) * δ^(-q)) := h6.symm
    _ ≤ ENNReal.ofReal (δ ^ (-(q + 2*κ0*qBox))) := h9

/-! ### Main wrapper -/

/-- `roundToDeltaGrid δ x` always lies on the δ-grid. -/
lemma roundToDeltaGrid_in_grid {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    robust_projection_main.roundToDeltaGrid δ x ∈ productLikeIntegerGrid δ := by
  refine ⟨round (x / δ), ?_⟩
  simp [robust_projection_main.roundToDeltaGrid, productLikeIntegerGrid]
  <;> rfl

/-- Normalize bounded E3' to [0,1]^2, call extraction bridge, denormalize.

Parameters:
- δ : original dyadic scale (δ ≤ 1)
- δ' := δ / L : normalized dyadic scale
- L = 2^k, R = L/2 = 2^{k-1} (positive integer for k ≥ 1)
- hR_int: R is a positive integer (ensures exact grid alignment and translation preservation)
- Energy bounds pre-computed at scale δ' for normalized projections
-/

lemma normalize_and_extract
    {δ κ0 η_total η_energy C_energy C_extract : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hkappa_pos : 0 < κ0) (hκ0_le_one : κ0 ≤ 1)
    (hη_total_pos : 0 < η_total) (hη_energy_pos : 0 < η_energy)
    (hδ_kappa_small : δ ^ κ0 ≤ 1 / 128)
    (hC_extract_pos : 0 < C_extract)
    (R L : ℝ) (k : ℕ)
    (hR_pos : 0 < R) (hL : L = (2 : ℝ) ^ k) (hL_2R : L = 2 * R)
    (hL_pos : 0 < L)
    (hR_int : ∃ (c : ℤ), R = (c : ℝ))
    (h_energy_absorb : C_energy * (δ / L) ^ (-η_total) ≤ (δ / L) ^ (-η_energy))
    (hC_extract_large : robust_projection_main.energyToLargeMassDeltaSetC (δ / L) κ0
        ((3 : ℝ) ^ (2 * κ0) * (δ / L) ^ (-η_energy)) ≤ C_extract)
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3']
    {E3' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_supp : μE3'.support = E3')
    (h_bound : ∀ p ∈ E3', |p 0| ≤ R ∧ |p 1| ≤ R)
    (h_energy_x_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 0)) μE3') ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total)))
    (h_energy_y_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 1)) μE3') ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total))) :
    ∃ (round : ℝ → ℝ) (S1 S2 : Set ℝ)
      (E3'' : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ x, |x - round x| ≤ δ / 2) ∧
      (∀ x, round x ∈ productLikeIntegerGrid δ) ∧
      S1 ⊆ productLikeIntegerGrid δ ∧
      S2 ⊆ productLikeIntegerGrid δ ∧
      (∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ) ∧
      (∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ) ∧
      S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 0)) E3' ∧
      S2 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 1)) E3' ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 ∧
      E3'' ⊆ E3' ∧
      μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) ∧
      (∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2) := by
  set δ' := δ / L with hδ'_def
  have hL_ge_two : L ≥ 2 := by
    rcases hR_int with ⟨c, hc⟩
    have h1 : 0 < c := by
      by_contra h2
      have h3 : c ≤ 0 := by omega
      have h4 : (c : ℝ) ≤ 0 := by exact_mod_cast h3
      rw [hc] at hR_pos
      exact False.elim (not_le.mpr hR_pos h4)
    have h2 : c ≥ 1 := by omega
    have h3 : (c : ℝ) ≥ 1 := by exact_mod_cast h2
    have h4 : R ≥ 1 := by
      have h5 : R = (c : ℝ) := hc
      rw [h5] <;> linarith
    calc L = 2 * R := hL_2R
         _ ≥ 2 * (1 : ℝ) := by gcongr
         _ = 2 := by norm_num
  have hL_gt_one : 1 < L := by linarith
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_dyadic : δ' ∈ dyadicScales := by
    have h1 : δ' = δ / (2 : ℝ) ^ k := by simp [hδ'_def, hL]
    rw [h1]
    exact dyadicScale_div_pow2 hδ_dyadic
  have hδ'_lt_one : δ' < 1 := by
    have h1 : δ / L ≤ δ / 2 := by
      gcongr
      <;> linarith [hL_ge_two]
    have h2 : δ' ≤ δ / 2 := by
      rw [hδ'_def] <;> exact h1
    have h3 : δ / 2 < 1 := by
      have h4 : 0 < δ := hδ_pos
      have h5 : δ ≤ 1 := hδ_le_one
      linarith
    linarith
  have hδ'_kappa_small : δ' ^ κ0 ≤ 1 / 128 := by
    have h1 : δ' ≤ δ := by
      rw [hδ'_def]
      have h2 : 1 ≤ L := by linarith
      have h3 : δ / L ≤ δ := by
        apply div_le_self <;> linarith
      exact h3
    have h4 : 0 ≤ δ' := by linarith
    have h5 : δ' ^ κ0 ≤ δ ^ κ0 := by
      have h51 : 0 ≤ δ' := by linarith
      have h52 : 0 ≤ κ0 := by linarith
      exact Real.rpow_le_rpow h51 h1 h52
    linarith [hδ_kappa_small]

  -- Define normalization map T on EuclideanSpace (coordinate-wise)
  -- Helper: EuclideanSpace.equiv symm preserves evaluation
  have hEquiv_symm : ∀ (f : Fin 2 → ℝ) (i : Fin 2),
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm f) i = f i := by
    intro f i
    simp

  let T : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => normalizeMap R L (p i))
  let Tinv : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun q => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => denormalizeMap R L (q i))

  have hT_apply : ∀ p i, (T p) i = normalizeMap R L (p i) := by
    intro p i; exact hEquiv_symm _ i
  have hTinv_apply : ∀ q i, (Tinv q) i = denormalizeMap R L (q i) := by
    intro q i; exact hEquiv_symm _ i

  have hT_left_inv : Function.LeftInverse Tinv T := by
    intro p
    ext i
    fin_cases i <;> rw [hTinv_apply, hT_apply, denormalizeMap_leftInverse hR_pos hL_2R]
  have hT_right_inv : Function.LeftInverse T Tinv := by
    intro q
    ext i
    fin_cases i <;> rw [hT_apply, hTinv_apply, normalizeMap_leftInverse hR_pos hL_2R]
  have hT_inj : Function.Injective T :=
    Function.LeftInverse.injective hT_left_inv

  have hT_cont : Continuous T := by
    have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => (fun i : Fin 2 => normalizeMap R L (p i))) := by
      apply continuous_pi
      intro i
      have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p i) := by
        exact PiLp.continuous_apply 2 (fun x => ℝ) i
      have h3 : Continuous (fun x : ℝ => (x + R) / L) := by
        continuity
      exact h3.comp h2
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp h1
  let E3_norm := T '' E3'
  let μ_norm := Measure.map T μE3'

  have hT_meas : Measurable T := hT_cont.measurable

  -- E3_norm is in [0,1]^2
  have hE3_norm_unit : ∀ q ∈ E3_norm, q 0 ∈ Set.Icc (0 : ℝ) 1 ∧ q 1 ∈ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    have hbx := h_bound p hp
    exact ⟨normalizeMap_range hR_pos hL_2R hbx.1, normalizeMap_range hR_pos hL_2R hbx.2⟩

  -- μ_norm is probability
  have hμ_norm_prob : IsProbabilityMeasure μ_norm := by
    refine' ⟨_⟩
    rw [Measure.map_apply hT_meas MeasurableSet.univ] <;> simp

  -- E3' is closed (support)
  have hE3'_closed : IsClosed E3' := by
    rw [←hE3'_supp]
    exact Measure.isClosed_support

  -- E3' is bounded
  have hE3'_bdd : Bornology.IsBounded E3' := by
    have h1 : E3' ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (2 * R) := by
      intro p hp
      have h := h_bound p hp
      have h2 : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
        have h21 := EuclideanSpace.real_norm_sq_eq p
        rw [h21, Fin.sum_univ_two] <;> ring
      have h3 : 0 ≤ R := by linarith
      have h4 : (p 0) ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp h.1]
      have h5 : (p 1) ^ 2 ≤ R ^ 2 := by nlinarith [abs_le.mp h.2]
      have h6 : ‖p‖ ^ 2 ≤ (2 * R) ^ 2 := by
        rw [h2] <;> nlinarith
      have h7 : 0 ≤ ‖p‖ := by positivity
      have h8 : ‖p‖ ≤ 2 * R := by nlinarith
      simpa [Metric.mem_closedBall, dist_zero_right] using h8
    exact Metric.isBounded_closedBall.subset h1

  -- E3' is compact
  have hE3'_compact : IsCompact E3' :=
    Metric.isCompact_of_isClosed_isBounded hE3'_closed hE3'_bdd

  -- E3_norm is closed (continuous image of compact)
  have hE3_norm_closed : IsClosed E3_norm :=
    (hE3'_compact.image hT_cont).isClosed

  -- μ_norm E3_norm = 1
  have h_preimage_eq : T ⁻¹' E3_norm = E3' := by
    ext x
    simp only [Set.mem_preimage, E3_norm, Set.mem_image]
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have h : T y = T x := hxy
      have h' : y = x := hT_inj h
      subst h'
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hμ_norm_E3_norm : μ_norm E3_norm = 1 := by
    rw [Measure.map_apply hT_meas hE3_norm_closed.measurableSet, h_preimage_eq]
    have h : μE3' E3' = 1 := by
      rw [←hE3'_supp]
      have h_prob : μE3' Set.univ = 1 := by exact measure_univ
      have h_supp_meas : MeasurableSet μE3'.support := Measure.isClosed_support.measurableSet
      have h_add : μE3' μE3'.support + μE3' (μE3'.support)ᶜ = μE3' Set.univ :=
        MeasureTheory.measure_add_measure_compl h_supp_meas
      have h_compl : μE3' (μE3'.support)ᶜ = 0 := μE3'.measure_compl_support
      rw [h_compl] at h_add
      simpa [h_prob] using h_add
    exact h

  -- Support equality: μ_norm.support = E3_norm
  have hE3_norm_supp : μ_norm.support = E3_norm := by
    -- Direction 1: support ⊆ E3_norm
    have h1 : μ_norm.support ⊆ E3_norm := by
      apply Measure.support_subset_of_isClosed hE3_norm_closed
      have h_compl : μ_norm E3_normᶜ = 0 := by
        have h_eq : μ_norm E3_normᶜ = μ_norm Set.univ - μ_norm E3_norm :=
          MeasureTheory.measure_compl hE3_norm_closed.measurableSet (by simp)
        rw [h_eq, hμ_norm_prob.measure_univ, hμ_norm_E3_norm]
        <;> simp
      have h_ae : E3_norm ∈ MeasureTheory.ae μ_norm := by
        simpa [MeasureTheory.mem_ae_iff] using h_compl
      exact h_ae
    -- Direction 2: E3_norm ⊆ support
    have h2 : E3_norm ⊆ μ_norm.support := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx_supp : x ∈ μE3'.support := by
        rw [hE3'_supp] <;> exact hx
      rw [Measure.support_eq_forall_isOpen]
      intro U hUy hU_open
      have h3 : IsOpen (T ⁻¹' U) := hU_open.preimage hT_cont
      have h4 : x ∈ T ⁻¹' U := hUy
      have h5 : 0 < μE3' (T ⁻¹' U) := by
        have h6 : x ∈ μE3'.support := hx_supp
        rw [Measure.support_eq_forall_isOpen] at h6
        exact h6 (T ⁻¹' U) h4 h3
      have h7 : μ_norm U = μE3' (T ⁻¹' U) := by
        rw [Measure.map_apply hT_meas hU_open.measurableSet] <;> rfl
      rw [h7] <;> exact h5
    apply Set.Subset.antisymm h1 h2

  -- Projections
  let proj_x_norm : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 0
  let proj_y_norm : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 1
  have h_proj_x_meas : Measurable proj_x_norm := by fun_prop
  have h_proj_y_meas : Measurable proj_y_norm := by fun_prop

  -- Energy composition: map proj_x_norm (map T μE3') = map (proj_x_norm ∘ T) μE3'
  have h_energy_x : robust_projection_main.rieszEnergy (2 * κ0) hδ'_pos
      (Measure.map proj_x_norm μ_norm) ≤ ENNReal.ofReal (C_energy * δ' ^ (-η_total)) := by
    have h_eq : Measure.map proj_x_norm μ_norm =
        Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 0)) μE3' := by
      have h1 : Measure.map proj_x_norm μ_norm = Measure.map (proj_x_norm ∘ T) μE3' := by
        rw [← Measure.map_map h_proj_x_meas hT_meas] <;> rfl
      rw [h1]
      <;> rfl
    rw [h_eq]
    simpa [hδ'_def] using h_energy_x_norm

  have h_energy_y : robust_projection_main.rieszEnergy (2 * κ0) hδ'_pos
      (Measure.map proj_y_norm μ_norm) ≤ ENNReal.ofReal (C_energy * δ' ^ (-η_total)) := by
    have h_eq : Measure.map proj_y_norm μ_norm =
        Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 1)) μE3' := by
      have h1 : Measure.map proj_y_norm μ_norm = Measure.map (proj_y_norm ∘ T) μE3' := by
        rw [← Measure.map_map h_proj_y_meas hT_meas] <;> rfl
      rw [h1]
      <;> rfl
    rw [h_eq]
    simpa [hδ'_def] using h_energy_y_norm

  -- Rewrite hypotheses to use δ' instead of δ / L
  have h_energy_absorb' : C_energy * δ' ^ (-η_total) ≤ δ' ^ (-η_energy) := by
    simpa [hδ'_def] using h_energy_absorb
  have hC_extract_large' : robust_projection_main.energyToLargeMassDeltaSetC δ' κ0
      ((3 : ℝ) ^ (2 * κ0) * δ' ^ (-η_energy)) ≤ C_extract := by
    simpa [hδ'_def] using hC_extract_large

  -- Call the bridge on normalized data
  obtain ⟨round_norm, S1_norm, S2_norm, E3''_norm, h_round_eq, h_round_near,
      hS1_grid, hS2_grid, hS1_sep, hS2_sep,
      hS1_sub, hS2_sub, hS1_delta, hS2_delta,
      hE3''_sub, hE3''_mass, hE3''_round⟩ :=
    extract_A1_A2_bridge
      hδ'_pos hδ'_dyadic hδ'_lt_one
      hkappa_pos hκ0_le_one hη_total_pos hη_energy_pos
      hδ'_kappa_small hC_extract_pos h_energy_absorb' hC_extract_large'
      (μE3' := μ_norm) (hE3'_supp := hE3_norm_supp)
      (hE3'_unit := hE3_norm_unit)
      h_energy_x h_energy_y

  -- Denormalize outputs
  let round : ℝ → ℝ := fun x =>
    denormalizeMap R L (round_norm (normalizeMap R L x))
  let S1 : Set ℝ := (fun y => denormalizeMap R L y) '' S1_norm
  let S2 : Set ℝ := (fun y => denormalizeMap R L y) '' S2_norm
  let E3'' : Set (EuclideanSpace ℝ (Fin 2)) := Tinv '' E3''_norm

  have hδ_eq_Lδ' : δ = L * δ' := by
    simp [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring

  -- R is a positive integer
  rcases hR_int with ⟨R_int, hR_int_eq⟩
  have hR_int_pos : 0 < R_int := by
    by_contra h; have h' : R_int ≤ 0 := by linarith
    have h'' : (R_int : ℝ) ≤ 0 := by exact_mod_cast h'
    linarith [hR_pos, hR_int_eq]

  -- R/δ is an integer: R = c, δ = 2^{-n}, so R/δ = c * 2^n
  have hδ_dyadic_copy := hδ_dyadic
  rcases hδ_dyadic_copy with ⟨n, hn⟩
  let R_div_delta : ℤ := R_int * (2 ^ n : ℕ)
  have hR_div_delta_eq : R = δ * (R_div_delta : ℝ) := by
    have hδ_eq : δ = (2 : ℝ) ^ (-(n : ℤ)) := hn
    simp [hR_int_eq, hδ_eq, R_div_delta, zpow_neg, zpow_ofNat] <;> field_simp <;> ring

  -- Round near property: |x - round x| ≤ δ / 2
  have h_round_near' : ∀ x, |x - round x| ≤ δ / 2 := by
    intro x
    have h1 : |normalizeMap R L x - round_norm (normalizeMap R L x)| ≤ δ' / 2 :=
      h_round_near (normalizeMap R L x)
    have h2 : x - round x = L * (normalizeMap R L x - round_norm (normalizeMap R L x)) := by
      simp [round, normalizeMap, denormalizeMap]
      <;> ring_nf <;> field_simp [hL_pos.ne'] <;> ring
    rw [h2]
    have h3 : |L * (normalizeMap R L x - round_norm (normalizeMap R L x))| =
        L * |normalizeMap R L x - round_norm (normalizeMap R L x)| := by
      rw [abs_mul, abs_of_pos hL_pos]
    rw [h3]
    have h4 : L * (δ' / 2) = δ / 2 := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    have h5 : L * |normalizeMap R L x - round_norm (normalizeMap R L x)| ≤ L * (δ' / 2) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    rw [h4] at h5
    exact h5

  -- Grid property for S1
  have hS1_grid' : S1 ⊆ productLikeIntegerGrid δ := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have h4 : z ∈ productLikeIntegerGrid δ' := hS1_grid hz
    rcases h4 with ⟨m, hm⟩
    have h5 : denormalizeMap R L z = δ * ((m - R_div_delta : ℤ) : ℝ) := by
      have h6 : denormalizeMap R L z = L * z - R := by
        simp [denormalizeMap] <;> ring
      have h7 : L * δ' = δ := by
        rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
      rw [h6, hm, hR_div_delta_eq]
      have h8 : L * (δ' * (m : ℝ)) = (m : ℝ) * δ := by
        rw [←mul_assoc, h7] <;> ring
      rw [h8]
      <;> simp [mul_sub] <;> ring
    have h_goal : (fun y : ℝ => denormalizeMap R L y) z = δ * ((m - R_div_delta : ℤ) : ℝ) := by
      simpa using h5
    rw [h_goal]
    exact ⟨m - R_div_delta, by ring⟩

  -- Grid property for S2
  have hS2_grid' : S2 ⊆ productLikeIntegerGrid δ := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have h4 : z ∈ productLikeIntegerGrid δ' := hS2_grid hz
    rcases h4 with ⟨m, hm⟩
    have h5 : denormalizeMap R L z = δ * ((m - R_div_delta : ℤ) : ℝ) := by
      have h6 : denormalizeMap R L z = L * z - R := by
        simp [denormalizeMap] <;> ring
      have h7 : L * δ' = δ := by
        rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
      rw [h6, hm, hR_div_delta_eq]
      have h8 : L * (δ' * (m : ℝ)) = (m : ℝ) * δ := by
        rw [←mul_assoc, h7] <;> ring
      rw [h8]
      <;> simp [mul_sub] <;> ring
    have h_goal : (fun y : ℝ => denormalizeMap R L y) z = δ * ((m - R_div_delta : ℤ) : ℝ) := by
      simpa using h5
    rw [h_goal]
    exact ⟨m - R_div_delta, by ring⟩

  -- Separation for S1
  have hS1_sep' : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    rcases hx with ⟨zx, hzx, rfl⟩
    rcases hy with ⟨zy, hzy, rfl⟩
    have hne : zx ≠ zy := by
      intro h; apply hxy; simp [h]
    have h : |zx - zy| ≥ δ' := hS1_sep zx hzx zy hzy hne
    have h2 : |denormalizeMap R L zx - denormalizeMap R L zy| = L * |zx - zy| := by
      have h3 : denormalizeMap R L zx - denormalizeMap R L zy = L * (zx - zy) := by
        simp [denormalizeMap] <;> ring
      rw [h3, abs_mul, abs_of_pos hL_pos]
    rw [h2]
    have h3 : L * δ' = δ := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    have h4 : L * |zx - zy| ≥ L * δ' := mul_le_mul_of_nonneg_left h (by linarith)
    rw [h3] at h4
    exact h4

  -- Separation for S2
  have hS2_sep' : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    rcases hx with ⟨zx, hzx, rfl⟩
    rcases hy with ⟨zy, hzy, rfl⟩
    have hne : zx ≠ zy := by
      intro h; apply hxy; simp [h]
    have h : |zx - zy| ≥ δ' := hS2_sep zx hzx zy hzy hne
    have h2 : |denormalizeMap R L zx - denormalizeMap R L zy| = L * |zx - zy| := by
      have h3 : denormalizeMap R L zx - denormalizeMap R L zy = L * (zx - zy) := by
        simp [denormalizeMap] <;> ring
      rw [h3, abs_mul, abs_of_pos hL_pos]
    rw [h2]
    have h3 : L * δ' = δ := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    have h4 : L * |zx - zy| ≥ L * δ' := mul_le_mul_of_nonneg_left h (by linarith)
    rw [h3] at h4
    exact h4

  -- Subset property for S1
  have hS1_sub' : S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 0)) E3' := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have h5 : z ∈ round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) := by
      have h51 : z ∈ robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) := hS1_sub hz
      rw [h_round_eq] at *
      <;> exact h51
    rcases h5 with ⟨w, hw, hz_eq⟩
    rcases hw with ⟨q, hq, hw_eq⟩
    rcases hq with ⟨p, hp, hq_eq⟩
    have h6 : q = T p := hq_eq.symm
    have h_w_eq : w = normalizeMap R L (p.ofLp 0) := by
      have h7 : q.ofLp 0 = w := hw_eq
      have h8 : q.ofLp 0 = (T p).ofLp 0 := by rw [h6]
      have h9 : (T p).ofLp 0 = normalizeMap R L (p.ofLp 0) := hT_apply p 0
      rw [h8, h9] at h7
      exact h7.symm
    have h_goal : denormalizeMap R L (robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 0))) =
        denormalizeMap R L z := by
      have h10 : robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 0)) = z := by
        calc robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 0))
          _ = round_norm (normalizeMap R L (p.ofLp 0)) := by rw [←h_round_eq]
          _ = round_norm w := by rw [h_w_eq]
          _ = z := hz_eq
      rw [h10]
    have h_goal2 : round (p 0) = denormalizeMap R L z := by
      simp only [round]
      rw [h_round_eq]
      exact h_goal
    exact ⟨p, hp, h_goal2⟩

  -- Subset property for S2
  have hS2_sub' : S2 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 1)) E3' := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have h5 : z ∈ round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) := by
      have h51 : z ∈ robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) := hS2_sub hz
      rw [h_round_eq] at *
      <;> exact h51
    rcases h5 with ⟨w, hw, hz_eq⟩
    rcases hw with ⟨q, hq, hw_eq⟩
    rcases hq with ⟨p, hp, hq_eq⟩
    have h6 : q = T p := hq_eq.symm
    have h_w_eq : w = normalizeMap R L (p.ofLp 1) := by
      have h7 : q.ofLp 1 = w := hw_eq
      have h8 : q.ofLp 1 = (T p).ofLp 1 := by rw [h6]
      have h9 : (T p).ofLp 1 = normalizeMap R L (p.ofLp 1) := hT_apply p 1
      rw [h8, h9] at h7
      exact h7.symm
    have h_goal : denormalizeMap R L (robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 1))) =
        denormalizeMap R L z := by
      have h10 : robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 1)) = z := by
        calc robust_projection_main.roundToDeltaGrid δ' (normalizeMap R L (p.ofLp 1))
          _ = round_norm (normalizeMap R L (p.ofLp 1)) := by rw [←h_round_eq]
          _ = round_norm w := by rw [h_w_eq]
          _ = z := hz_eq
      rw [h10]
    have h_goal2 : round (p 1) = denormalizeMap R L z := by
      simp only [round]
      rw [h_round_eq]
      exact h_goal
    exact ⟨p, hp, h_goal2⟩

  -- Boundedness of S1_norm, S2_norm
  have hS1_norm_bdd : Bornology.IsBounded S1_norm := by
    have h6 : S1_norm ⊆ Set.Icc (-(δ' / 2)) (1 + δ' / 2) := by
      intro z hz
      have h7 : z ∈ round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) := by
        have h71 : z ∈ robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) := hS1_sub hz
        have h_eq : round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) =
            robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 0) '' E3_norm) := by
          rw [h_round_eq]
        rw [h_eq]
        exact h71
      rcases h7 with ⟨w, hw, rfl⟩
      have h8 : w ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hw with ⟨q, hq, rfl⟩
        exact (hE3_norm_unit q hq).1
      have h9 : |w - round_norm w| ≤ δ' / 2 := h_round_near w
      rcases abs_le.mp h9 with ⟨h11, h12⟩
      exact ⟨by linarith [h8.1], by linarith [h8.2]⟩
    have h7 : Bornology.IsBounded (Set.Icc (-(δ' / 2)) (1 + δ' / 2)) := by
      exact Metric.isBounded_Icc (-(δ' / 2)) (1 + δ' / 2)
    exact h7.subset h6

  have hS2_norm_bdd : Bornology.IsBounded S2_norm := by
    have h6 : S2_norm ⊆ Set.Icc (-(δ' / 2)) (1 + δ' / 2) := by
      intro z hz
      have h7 : z ∈ round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) := by
        have h71 : z ∈ robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) := hS2_sub hz
        have h_eq : round_norm '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) =
            robust_projection_main.roundToDeltaGrid δ' '' ((fun p : EuclideanSpace ℝ (Fin 2) => p.ofLp 1) '' E3_norm) := by
          rw [h_round_eq]
        rw [h_eq]
        exact h71
      rcases h7 with ⟨w, hw, rfl⟩
      have h8 : w ∈ Set.Icc (0 : ℝ) 1 := by
        rcases hw with ⟨q, hq, rfl⟩
        exact (hE3_norm_unit q hq).2
      have h9 : |w - round_norm w| ≤ δ' / 2 := h_round_near w
      rcases abs_le.mp h9 with ⟨h11, h12⟩
      exact ⟨by linarith [h8.1], by linarith [h8.2]⟩
    have h7 : Bornology.IsBounded (Set.Icc (-(δ' / 2)) (1 + δ' / 2)) := by exact Metric.isBounded_Icc (-(δ' / 2)) (1 + δ' / 2)
    exact h7.subset h6

  -- Delta-SC property for S1: scale up then translate by -R
  have hS1_scaled_delta_raw : IsProductLikeRealDeltaSCSet (L * δ') κ0 C_extract (scaleSet L S1_norm) :=
    have hκ0_nonneg : 0 ≤ κ0 := by linarith
    have hLδ'_eq : L * δ' = δ := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    have hLδ'_dyadic : (L * δ') ∈ dyadicScales := by
      rw [hLδ'_eq] <;> exact hδ_dyadic
    have hLδ'_le_one : L * δ' ≤ 1 := by
      rw [hLδ'_eq] <;> exact hδ_le_one
    deltaSCSet_scale_up hδ'_pos hδ'_dyadic hκ0_nonneg hC_extract_pos L k hL
      hLδ'_dyadic hLδ'_le_one hS1_norm_bdd hS1_delta
  have hLδ'_eq : L * δ' = δ := by
    rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
  have hS1_scaled_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract (scaleSet L S1_norm) := by
    rw [hLδ'_eq] at hS1_scaled_delta_raw
    exact hS1_scaled_delta_raw

  have hS1_eq : S1 = translateSet (-(R_int : ℝ)) (scaleSet L S1_norm) := by
    ext y
    simp only [S1, scaleSet, translateSet, Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨L * z, ⟨z, hz, rfl⟩, by simp [denormalizeMap, hR_int_eq] <;> ring⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp [denormalizeMap, hR_int_eq] <;> ring⟩

  have hS1_delta' : IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 := by
    have h_translate_eq : translateSet (-(R_int : ℝ)) (scaleSet L S1_norm) =
        translateSet ((-R_int : ℤ) : ℝ) (scaleSet L S1_norm) := by
      congr
      <;> simp
    rw [hS1_eq, h_translate_eq]
    exact isProductLikeRealDeltaSCSet_translate_by_int (-R_int)
      hδ_dyadic hδ_pos hS1_scaled_delta

  -- Delta-SC property for S2
  have hS2_scaled_delta_raw : IsProductLikeRealDeltaSCSet (L * δ') κ0 C_extract (scaleSet L S2_norm) :=
    have hκ0_nonneg : 0 ≤ κ0 := by linarith
    have hLδ'_eq2 : L * δ' = δ := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    have hLδ'_dyadic : (L * δ') ∈ dyadicScales := by
      rw [hLδ'_eq2] <;> exact hδ_dyadic
    have hLδ'_le_one : L * δ' ≤ 1 := by
      rw [hLδ'_eq2] <;> exact hδ_le_one
    deltaSCSet_scale_up hδ'_pos hδ'_dyadic hκ0_nonneg hC_extract_pos L k hL
      hLδ'_dyadic hLδ'_le_one hS2_norm_bdd hS2_delta
  have hS2_scaled_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract (scaleSet L S2_norm) := by
    have hLδ'_eq2 : L * δ' = δ := by
      rw [hδ'_def] <;> field_simp [hL_pos.ne'] <;> ring
    rw [hLδ'_eq2] at hS2_scaled_delta_raw
    exact hS2_scaled_delta_raw

  have hS2_eq : S2 = translateSet (-(R_int : ℝ)) (scaleSet L S2_norm) := by
    ext y
    simp only [S2, scaleSet, translateSet, Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨L * z, ⟨z, hz, rfl⟩, by simp [denormalizeMap, hR_int_eq] <;> ring⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp [denormalizeMap, hR_int_eq] <;> ring⟩

  have hS2_delta' : IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 := by
    have h_translate_eq : translateSet (-(R_int : ℝ)) (scaleSet L S2_norm) =
        translateSet ((-R_int : ℤ) : ℝ) (scaleSet L S2_norm) := by
      congr
      <;> simp
    rw [hS2_eq, h_translate_eq]
    exact isProductLikeRealDeltaSCSet_translate_by_int (-R_int)
      hδ_dyadic hδ_pos hS2_scaled_delta

  -- E3'' subset E3'
  have hE3''_sub' : E3'' ⊆ E3' := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have h10 : q ∈ E3_norm := hE3''_sub hq
    rcases h10 with ⟨p', hp', h_eq⟩
    have h11 : Tinv q = p' := by
      have h12 : T p' = q := h_eq
      have h13 : Tinv q = Tinv (T p') := by rw [h12]
      rw [h13, hT_left_inv p']
    rw [h11]
    exact hp'

  -- E3'' mass
  have hE3''_mass' : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h12 : E3'' = Tinv '' E3''_norm := rfl
    rw [h12]
    have h13 : Tinv '' E3''_norm = T ⁻¹' E3''_norm := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, h_eq⟩
        have h14 : T x = y := by
          rw [←h_eq]
          exact hT_right_inv y
        rw [h14]
        exact hy
      · intro hx
        refine ⟨T x, hx, ?_⟩
        exact hT_left_inv x
    rw [h13]
    have hTinv_meas : Measurable Tinv := by
      have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => (fun i : Fin 2 => denormalizeMap R L (p i))) := by
        apply continuous_pi
        intro i
        have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin 2) => p i) := by exact PiLp.continuous_apply 2 (fun x => ℝ) i
        have h3 : Continuous (fun x : ℝ => L * x - R) :=
          (continuous_id.const_mul L).sub continuous_const
        exact h3.comp h2
      have h4 : Continuous Tinv := (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp h1
      exact h4.measurable
    let e : MeasurableEquiv (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
      { toFun := T, invFun := Tinv,
        left_inv := hT_left_inv, right_inv := hT_right_inv,
        measurable_toFun := hT_meas,
        measurable_invFun := hTinv_meas }
    have h14 : μE3' (T ⁻¹' E3''_norm) = μ_norm E3''_norm := by
      have h15 : μ_norm = Measure.map T μE3' := by rfl
      rw [h15]
      exact (MeasurableEquiv.map_apply e E3''_norm).symm
    rw [h14]
    exact hE3''_mass

  -- E3'' round capture
  have hE3''_round' : ∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2 := by
    intro p hp
    rcases hp with ⟨q, hq, rfl⟩
    have h14 : round_norm (q 0) ∈ S1_norm ∧ round_norm (q 1) ∈ S2_norm :=
      hE3''_round q hq
    constructor
    · have h16 : round ((Tinv q) 0) = denormalizeMap R L (round_norm (q 0)) := by
        have h17 : (Tinv q) 0 = denormalizeMap R L (q 0) := hTinv_apply q 0
        have h18 : normalizeMap R L (denormalizeMap R L (q 0)) = q 0 :=
          normalizeMap_leftInverse hR_pos hL_2R (q 0)
        calc round ((Tinv q) 0)
          _ = round (denormalizeMap R L (q 0)) := by rw [h17]
          _ = denormalizeMap R L (round_norm (normalizeMap R L (denormalizeMap R L (q 0)))) := by
            simp only [round]
            <;> rfl
          _ = denormalizeMap R L (round_norm (q 0)) := by rw [h18]
      rw [h16]
      exact ⟨round_norm (q 0), h14.1, rfl⟩
    · have h17 : round ((Tinv q) 1) = denormalizeMap R L (round_norm (q 1)) := by
        have h18 : (Tinv q) 1 = denormalizeMap R L (q 1) := hTinv_apply q 1
        have h19 : normalizeMap R L (denormalizeMap R L (q 1)) = q 1 :=
          normalizeMap_leftInverse hR_pos hL_2R (q 1)
        calc round ((Tinv q) 1)
          _ = round (denormalizeMap R L (q 1)) := by rw [h18]
          _ = denormalizeMap R L (round_norm (normalizeMap R L (denormalizeMap R L (q 1)))) := by
            simp only [round]
            <;> rfl
          _ = denormalizeMap R L (round_norm (q 1)) := by rw [h19]
      rw [h17]
      exact ⟨round_norm (q 1), h14.2, rfl⟩

  -- Grid property for round: round_norm maps to δ'-grid, denormalization maps to δ-grid
  have hround_grid' : ∀ x, round x ∈ productLikeIntegerGrid δ := by
    intro x
    let y := normalizeMap R L x
    have h1 : round_norm y ∈ productLikeIntegerGrid δ' := by
      have h2 : round_norm = robust_projection_main.roundToDeltaGrid δ' := h_round_eq
      rw [h2]
      exact roundToDeltaGrid_in_grid hδ'_pos y
    rcases h1 with ⟨m, hm : round_norm y = δ' * (m : ℝ)⟩
    have h3 : round x = denormalizeMap R L (round_norm y) := by rfl
    rw [h3, hm]
    have h4 : denormalizeMap R L (δ' * (m : ℝ)) = δ * ((m - R_div_delta : ℤ) : ℝ) := by
      have h5 : denormalizeMap R L (δ' * (m : ℝ)) = L * (δ' * (m : ℝ)) - R := by
        simp [denormalizeMap] <;> ring
      rw [h5, hR_div_delta_eq]
      have h6 : L * δ' = δ := by
        exact hδ_eq_Lδ'.symm
      have h7 : L * (δ' * (m : ℝ)) = δ * (m : ℝ) := by
        calc L * (δ' * (m : ℝ)) = (L * δ') * (m : ℝ) := by ring
             _ = δ * (m : ℝ) := by rw [h6] <;> ring
      rw [h7]
      simp [sub_mul] <;> ring
    rw [h4]
    exact ⟨m - R_div_delta, by ring⟩

  exact ⟨round, S1, S2, E3'', h_round_near', hround_grid', hS1_grid', hS2_grid', hS1_sep', hS2_sep',
    hS1_sub', hS2_sub', hS1_delta', hS2_delta', hE3''_sub', hE3''_mass', hE3''_round'⟩

/-- High-level wrapper: takes original-scale energy bounds and uses the energy bridge
to convert them to normalized scale before calling `normalize_and_extract`.

The condition `2 * κ0 ≤ η_total` accounts for the `L^{2κ0}` energy scaling factor
(the "qBox cost"). -/
lemma normalize_and_extract_with_energy_bridge
    {δ κ0 η_total η_energy C_energy C_extract : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_le_one : δ ≤ 1)
    (hkappa_pos : 0 < κ0) (hκ0_le_one : κ0 ≤ 1)
    (hη_total_pos : 0 < η_total) (hη_energy_pos : 0 < η_energy)
    (hδ_kappa_small : δ ^ κ0 ≤ 1 / 128)
    (hC_extract_pos : 0 < C_extract)
    (hC_energy_pos : 0 < C_energy)
    (h2κ0_le_ηtotal : 2 * κ0 ≤ η_total)
    (R L : ℝ) (k : ℕ)
    (hR_pos : 0 < R) (hL : L = (2 : ℝ) ^ k) (hL_2R : L = 2 * R)
    (hL_pos : 0 < L)
    (hR_int : ∃ (c : ℤ), R = (c : ℝ))
    (h_energy_absorb : C_energy * (δ / L) ^ (-η_total) ≤ (δ / L) ^ (-η_energy))
    (hC_extract_large : robust_projection_main.energyToLargeMassDeltaSetC (δ / L) κ0
        ((3 : ℝ) ^ (2 * κ0) * (δ / L) ^ (-η_energy)) ≤ C_extract)
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3']
    {E3' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_supp : μE3'.support = E3')
    (h_bound : ∀ p ∈ E3', |p 0| ≤ R ∧ |p 1| ≤ R)
    (h_energy_x_orig : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0) μE3') ≤
      ENNReal.ofReal (C_energy * δ ^ (-η_total)))
    (h_energy_y_orig : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3') ≤
      ENNReal.ofReal (C_energy * δ ^ (-η_total))) :
    ∃ (round : ℝ → ℝ) (S1 S2 : Set ℝ)
      (E3'' : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ x, |x - round x| ≤ δ / 2) ∧
      (∀ x, round x ∈ productLikeIntegerGrid δ) ∧
      S1 ⊆ productLikeIntegerGrid δ ∧
      S2 ⊆ productLikeIntegerGrid δ ∧
      (∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ) ∧
      (∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ) ∧
      S1 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 0)) E3' ∧
      S2 ⊆ Set.image (fun p : EuclideanSpace ℝ (Fin 2) => round (p 1)) E3' ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 ∧
      E3'' ⊆ E3' ∧
      μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) ∧
      (∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2) := by
  have hL_ge_one : 1 ≤ L := by
    rcases hR_int with ⟨c, hc⟩
    have h1 : 0 < c := by
      by_contra h2; have h3 : c ≤ 0 := by omega
      have h4 : (c : ℝ) ≤ 0 := by exact_mod_cast h3
      rw [hc] at hR_pos; exact False.elim (not_le.mpr hR_pos h4)
    have h2 : c ≥ 1 := by omega
    have h3 : (c : ℝ) ≥ 1 := by exact_mod_cast h2
    have h4 : R ≥ 1 := by rw [hc] <;> linarith
    have h5 : L ≥ 2 := by
      calc L = 2 * R := hL_2R
           _ ≥ 2 * (1 : ℝ) := by gcongr
           _ = 2 := by norm_num
    linarith
  let ν_x : Measure ℝ := Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0) μE3'
  let ν_y : Measure ℝ := Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3'
  have h_proj0_meas : Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p 0) := by fun_prop
  have h_proj1_meas : Measurable (fun p : EuclideanSpace ℝ (Fin 2) => p 1) := by fun_prop
  have h_norm_meas : Measurable (normalizeMap R L) := by
    have h_cont : Continuous (fun x : ℝ => (x + R) / L) := by continuity
    have h_eq : (normalizeMap R L) = (fun x : ℝ => (x + R) / L) := by funext x; simp [normalizeMap]
    rw [h_eq]; exact h_cont.measurable
  have h_map_x_eq : Measure.map (normalizeMap R L) ν_x =
      Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 0)) μE3' := by
    dsimp only [ν_x]
    have h : Measure.map (normalizeMap R L) (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0) μE3') =
        Measure.map ((normalizeMap R L) ∘ (fun p : EuclideanSpace ℝ (Fin 2) => p 0)) μE3' :=
      Measure.map_map h_norm_meas h_proj0_meas
    rw [h]
    <;> rfl
  have h_map_y_eq : Measure.map (normalizeMap R L) ν_y =
      Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 1)) μE3' := by
    dsimp only [ν_y]
    have h : Measure.map (normalizeMap R L) (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 1) μE3') =
        Measure.map ((normalizeMap R L) ∘ (fun p : EuclideanSpace ℝ (Fin 2) => p 1)) μE3' :=
      Measure.map_map h_norm_meas h_proj1_meas
    rw [h]
    <;> rfl
  have h_energy_x_norm0 := normalized_energy_bridge hδ_pos hkappa_pos hη_total_pos h2κ0_le_ηtotal
    R L hR_pos hL_2R hL_pos hL_ge_one hC_energy_pos (ν := ν_x) h_energy_x_orig
  have h_energy_y_norm0 := normalized_energy_bridge hδ_pos hkappa_pos hη_total_pos h2κ0_le_ηtotal
    R L hR_pos hL_2R hL_pos hL_ge_one hC_energy_pos (ν := ν_y) h_energy_y_orig
  have h_energy_x_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 0)) μE3') ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total)) := by
    rw [←h_map_x_eq]; exact h_energy_x_norm0
  have h_energy_y_norm : robust_projection_main.rieszEnergy (2 * κ0) (div_pos hδ_pos hL_pos)
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => normalizeMap R L (p 1)) μE3') ≤
      ENNReal.ofReal (C_energy * (δ / L) ^ (-η_total)) := by
    rw [←h_map_y_eq]; exact h_energy_y_norm0
  exact normalize_and_extract hδ_pos hδ_dyadic hδ_le_one hkappa_pos hκ0_le_one
    hη_total_pos hη_energy_pos hδ_kappa_small hC_extract_pos
    R L k hR_pos hL hL_2R hL_pos hR_int
    h_energy_absorb hC_extract_large
    (hE3'_supp := hE3'_supp) (h_bound := h_bound)
    h_energy_x_norm h_energy_y_norm

end ProductLikeIncidence.ProductReduction
