module

/-
# Phase 8 — Sector Translation Main Theorem

Bridge from BSG sector output to Ring theorem input.

## Sector normalization (UNTRANSLATED output)

Returns `B_ring0` (before integer shift), `B_coord`, and `c : ℤ` such that
`translateSet c B_ring0 ⊆ [1,2]`. The caller (Phase9) performs the translation
internally; passing an already-translated set would translate twice.

- Sector 0: B_ring0 = B2,     B_coord = B1, c = 1
- Sector 1: B_ring0 = B1,     B_coord = B2, c = 1
- Sector 2: B_ring0 = -B2,    B_coord = B1, c = 2
- Sector 3: B_ring0 = -B1,    B_coord = B2, c = 2

Reflection (sectors 2,3) doubles the δ-set constant. The input hypotheses
`2*C_B ≤ K_work * δ^(-εnc)` absorb this factor, so the output uses the
consistent global constant `K_work`.

## Whiteprint node
`phase8_sector_translation`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace ProductLikeIncidence

/-! ### Sector definitions -/

def sectorProductSet (i : Fin 4) (B1 B2 : Set ℝ) : Set (ℝ × ℝ) :=
  match i with
  | 0 => B2 ×ˢ B1
  | 1 => B1 ×ˢ B2
  | 2 => (Set.image (fun x => -x) B2) ×ˢ B1
  | 3 => (Set.image (fun x => -x) B1) ×ˢ B2

/-- Untranslated ring base set (before integer shift). -/
def sectorRingBaseSet (i : Fin 4) (B1 B2 : Set ℝ) : Set ℝ :=
  match i with
  | 0 => B2
  | 1 => B1
  | 2 => Set.image (fun x => -x) B2
  | 3 => Set.image (fun x => -x) B1

def sectorShift (i : Fin 4) : ℤ :=
  match i with
  | 0 => 1 | 1 => 1 | 2 => 2 | 3 => 2

def sectorCoordSet (i : Fin 4) (B1 B2 : Set ℝ) : Set ℝ :=
  match i with
  | 0 => B1 | 1 => B2 | 2 => B1 | 3 => B2

lemma sectorProductSet_eq (i : Fin 4) (B1 B2 : Set ℝ) :
    sectorProductSet i B1 B2 = sectorRingBaseSet i B1 B2 ×ˢ sectorCoordSet i B1 B2 := by
  fin_cases i <;> simp [sectorProductSet, sectorRingBaseSet, sectorCoordSet] <;> rfl

/-! ### Difference set helper lemmas -/

/-- `T - (-S) = T + S` as sets. -/
lemma diff_neg_eq_add {S T : Set ℝ} :
    Set.image2 (· - ·) T (Set.image (fun x => -x) S) = Set.image2 (· + ·) T S := by
  ext z
  simp only [Set.mem_image2, Set.mem_image]
  constructor
  · rintro ⟨t, ht, y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨t, ht, u, hu, by ring⟩
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact ⟨t, ht, -u, ⟨u, hu, rfl⟩, by ring⟩

/-- `Nδ((-S)-(-S)) = Nδ(S-S)` via exact reflection on grid sets. -/
lemma neg_diff_eq {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Set ℝ} (hS_grid : S ⊆ productLikeIntegerGrid δ)
    (hS_bdd : Bornology.IsBounded S) :
    Nreal δ (Set.image2 (· - ·) (Set.image (fun x => -x) S) (Set.image (fun x => -x) S)) =
    Nreal δ (Set.image2 (· - ·) S S) := by
  have h3 : Set.image2 (· - ·) (Set.image (fun x => -x) S) (Set.image (fun x => -x) S) =
      Set.image (fun x : ℝ => -x) (Set.image2 (· - ·) S S) := by
    ext z
    simp only [Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x - y, ⟨x, hx, y, hy, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨-x, ⟨x, hx, rfl⟩, -y, ⟨y, hy, rfl⟩, by ring⟩
  rw [h3]
  have h4 : (Set.image2 (· - ·) S S) ⊆ productLikeIntegerGrid δ := by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    have h_a : ∃ (k : ℤ), a = δ * (k : ℝ) := hS_grid ha
    have h_b : ∃ (j : ℤ), b = δ * (j : ℝ) := hS_grid hb
    rcases h_a with ⟨k, hk⟩
    rcases h_b with ⟨j, hj⟩
    refine ⟨k - j, ?_⟩
    have h_eq : a - b = δ * ((k - j : ℤ) : ℝ) := by
      rw [hk, hj] <;> simp [mul_comm] <;> ring
    exact h_eq
  have h5 : Bornology.IsBounded (Set.image2 (· - ·) S S) := hS_bdd.sub hS_bdd
  exact nreal_reflection_eq hδ_pos h4 h5

/-- `Nδ(T-S) = Nδ(S-T)` via exact reflection on grid sets. -/
lemma cross_neg_eq {δ : ℝ} (hδ_pos : 0 < δ)
    {S T : Set ℝ} (hS_grid : S ⊆ productLikeIntegerGrid δ)
    (hT_grid : T ⊆ productLikeIntegerGrid δ)
    (hS_bdd : Bornology.IsBounded S) (hT_bdd : Bornology.IsBounded T) :
    Nreal δ (Set.image2 (· - ·) T S) = Nreal δ (Set.image2 (· - ·) S T) := by
  have h3 : Set.image2 (· - ·) T S =
      Set.image (fun x : ℝ => -x) (Set.image2 (· - ·) S T) := by
    ext z
    simp only [Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨t, ht, s, hs, rfl⟩
      exact ⟨s - t, ⟨s, hs, t, ht, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨s, hs, t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, s, hs, by ring⟩
  rw [h3]
  have h4 : (Set.image2 (· - ·) S T) ⊆ productLikeIntegerGrid δ := by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    have h_a : ∃ (k : ℤ), a = δ * (k : ℝ) := hS_grid ha
    have h_b : ∃ (j : ℤ), b = δ * (j : ℝ) := hT_grid hb
    rcases h_a with ⟨k, hk⟩
    rcases h_b with ⟨j, hj⟩
    refine ⟨k - j, ?_⟩
    have h_eq : a - b = δ * ((k - j : ℤ) : ℝ) := by
      rw [hk, hj] <;> simp [mul_comm] <;> ring
    exact h_eq
  have h5 : Bornology.IsBounded (Set.image2 (· - ·) S T) := hS_bdd.sub hT_bdd
  exact nreal_reflection_eq hδ_pos h4 h5

/-- `translateSet (sectorShift i) (sectorRingBaseSet i B1 B2) ⊆ [1,2]`. -/
lemma sector_translate_subset {δ : ℝ} {B1 B2 : Set ℝ}
    (hB1_grid : B1 ⊆ productLikeUnitGrid δ)
    (hB2_grid : B2 ⊆ productLikeUnitGrid δ)
    (i : Fin 4) :
    ProductReduction.translateSet (sectorShift i : ℝ) (sectorRingBaseSet i B1 B2) ⊆ Set.Icc (1 : ℝ) 2 := by
  fin_cases i
  · -- Sector 0: B2 + 1
    intro x hx
    rcases hx with ⟨y, hy, h_eq⟩
    have h0 : 0 ≤ y := (hB2_grid hy).2.1
    have h1 : y ≤ 1 := (hB2_grid hy).2.2
    have h_main : 1 ≤ y + 1 ∧ y + 1 ≤ 2 := ⟨by linarith [h0], by linarith [h1]⟩
    have h_eq' : x = y + 1 := by simpa [sectorShift] using h_eq.symm
    exact Set.mem_Icc.mpr (h_eq' ▸ h_main)
  · -- Sector 1: B1 + 1
    intro x hx
    rcases hx with ⟨y, hy, h_eq⟩
    have h0 : 0 ≤ y := (hB1_grid hy).2.1
    have h1 : y ≤ 1 := (hB1_grid hy).2.2
    have h_main : 1 ≤ y + 1 ∧ y + 1 ≤ 2 := ⟨by linarith [h0], by linarith [h1]⟩
    have h_eq' : x = y + 1 := by simpa [sectorShift] using h_eq.symm
    exact Set.mem_Icc.mpr (h_eq' ▸ h_main)
  · -- Sector 2: -B2 + 2
    intro x hx
    rcases hx with ⟨y, hy, h_eq⟩
    rcases hy with ⟨z, hz, h_y_eq⟩
    have h0 : 0 ≤ z := (hB2_grid hz).2.1
    have h1 : z ≤ 1 := (hB2_grid hz).2.2
    have hy_eq : y = -z := h_y_eq.symm
    have h_goal : 1 ≤ y + 2 ∧ y + 2 ≤ 2 := by
      rw [hy_eq]
      exact ⟨by linarith [h0, h1], by linarith [h0, h1]⟩
    have h_final : y + 2 = x := h_eq
    rw [h_final] at h_goal
    exact Set.mem_Icc.mpr h_goal
  · -- Sector 3: -B1 + 2
    intro x hx
    rcases hx with ⟨y, hy, h_eq⟩
    rcases hy with ⟨z, hz, h_y_eq⟩
    have h0 : 0 ≤ z := (hB1_grid hz).2.1
    have h1 : z ≤ 1 := (hB1_grid hz).2.2
    have hy_eq : y = -z := h_y_eq.symm
    have h_goal : 1 ≤ y + 2 ∧ y + 2 ≤ 2 := by
      rw [hy_eq]
      exact ⟨by linarith [h0, h1], by linarith [h0, h1]⟩
    have h_final : y + 2 = x := h_eq
    rw [h_final] at h_goal
    exact Set.mem_Icc.mpr h_goal

/-! ### Main theorem -/

/-- **Phase 8 sector translation bridge (corrected interface)**

Given BSG-extracted B1, B2 with `(δ, κ0)`-set regularity, size bounds, and
difference/sumset bounds, select the sector normalization and output:

- `B_ring0`: UNTRANSLATED first set (raw or negated, depending on sector)
- `B_coord`: second set
- `c : ℤ`: integer shift such that `translateSet c B_ring0 ⊆ [1,2]`
- Regularity and size bounds on `B_ring0`
- Two difference bounds normalized by `N(B_ring0)`
- `G ⊆ B_ring0 ×ˢ B_coord`

The caller (Phase9) translates `B_ring0` by `c` internally. Do NOT translate
before passing to Phase9, or the translation will be applied twice.

Reflection in sectors 2,3 doubles the δ-set constant; the input hypotheses
`2*C_B ≤ K_work * δ^(-εnc)` absorb this so the output uses `K_work` uniformly.
-/
theorem phase8_sector_translation_main
    {δ s κ0 εnc C_B1 C_B2 K_work : ℝ}
    {B1 B2 : Set ℝ} {G : Set (ℝ × ℝ)}
    (sector_idx : Fin 4)
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hB1_grid : B1 ⊆ productLikeUnitGrid δ)
    (hB2_grid : B2 ⊆ productLikeUnitGrid δ)
    (hB1_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 C_B1 B1)
    (hB2_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 C_B2 B2)
    (hB1_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B1)
    (hB1_upper : Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB2_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B2)
    (hB2_upper : Nreal δ B2 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hC1_absorb : 2 * C_B1 ≤ K_work * δ ^ (-εnc))
    (hC2_absorb : 2 * C_B2 ≤ K_work * δ ^ (-εnc))
    (h_diff_B1B1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_diff_B2B2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_work * Nreal δ B2)
    (h_diff_B2B1_over_B1 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_diff_B2B1_over_B2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_work * Nreal δ B2)
    (h_sum_B1B2_over_B1 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_sum_B1B2_over_B2 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_work * Nreal δ B2)
    (hG_sector : G ⊆ sectorProductSet sector_idx B1 B2) :
    ∃ (B_ring0 B_coord : Set ℝ) (c : ℤ),
      ProductReduction.translateSet (c : ℝ) B_ring0 ⊆ Set.Icc (1 : ℝ) 2 ∧
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) B_ring0 ∧
      ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B_ring0 ∧
      Nreal δ B_ring0 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) ∧
      Nreal δ (Set.image2 (· - ·) B_ring0 B_ring0) ≤ ENNReal.ofReal K_work * Nreal δ B_ring0 ∧
      Nreal δ (Set.image2 (· - ·) B_coord B_ring0) ≤ ENNReal.ofReal K_work * Nreal δ B_ring0 ∧
      B_ring0 = sectorRingBaseSet sector_idx B1 B2 ∧
      B_coord = sectorCoordSet sector_idx B1 B2 ∧
      G ⊆ B_ring0 ×ˢ B_coord := by
  -- Setup: grid, boundedness
  have hB1_intgrid : B1 ⊆ productLikeIntegerGrid δ := fun x hx => (hB1_grid hx).1
  have hB2_intgrid : B2 ⊆ productLikeIntegerGrid δ := fun x hx => (hB2_grid hx).1
  have hB1_bdd : Bornology.IsBounded B1 := by
    rw [Metric.isBounded_iff]
    refine ⟨1, fun x hx y hy => ?_⟩
    have hx1 : 0 ≤ x := (hB1_grid hx).2.1
    have hx2 : x ≤ 1 := (hB1_grid hx).2.2
    have hy1 : 0 ≤ y := (hB1_grid hy).2.1
    have hy2 : y ≤ 1 := (hB1_grid hy).2.2
    rw [Real.dist_eq, abs_le] <;> constructor <;> linarith
  have hB2_bdd : Bornology.IsBounded B2 := by
    rw [Metric.isBounded_iff]
    refine ⟨1, fun x hx y hy => ?_⟩
    have hx1 : 0 ≤ x := (hB2_grid hx).2.1
    have hx2 : x ≤ 1 := (hB2_grid hx).2.2
    have hy1 : 0 ≤ y := (hB2_grid hy).2.1
    have hy2 : y ≤ 1 := (hB2_grid hy).2.2
    rw [Real.dist_eq, abs_le] <;> constructor <;> linarith
  -- Extract positivity of C constants
  have hC1_pos : 0 < C_B1 := by
    have h := hB1_kappa0
    rcases h with ⟨_, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  have hC2_pos : 0 < C_B2 := by
    have h := hB2_kappa0
    rcases h with ⟨_, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  -- For non-reflected sectors, C_B ≤ K_work * δ^(-εnc) follows from 2*C_B ≤ ...
  have hC1_le : C_B1 ≤ K_work * δ ^ (-εnc) := by
    have h : C_B1 ≤ 2 * C_B1 := by linarith
    linarith [hC1_absorb]
  have hC2_le : C_B2 ≤ K_work * δ ^ (-εnc) := by
    have h : C_B2 ≤ 2 * C_B2 := by linarith
    linarith [hC2_absorb]

  let c : ℤ := sectorShift sector_idx
  let B_ring0 : Set ℝ := sectorRingBaseSet sector_idx B1 B2
  let B_coord : Set ℝ := sectorCoordSet sector_idx B1 B2

  -- Goal 1: translateSet c B_ring0 ⊆ [1,2]
  have h_translate_subset : ProductReduction.translateSet (c : ℝ) B_ring0 ⊆ Set.Icc (1 : ℝ) 2 :=
    sector_translate_subset hB1_grid hB2_grid sector_idx

  -- Goal 2: δ-set property on B_ring0
  have h_delta : IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) B_ring0 := by
    fin_cases sector_idx
    · -- Sector 0: B_ring0 = B2, no reflection
      dsimp only [B_ring0, sectorRingBaseSet]
      exact IsDeltaSCSet.mono hB2_kappa0 hC2_le
    · -- Sector 1: B_ring0 = B1, no reflection
      dsimp only [B_ring0, sectorRingBaseSet]
      exact IsDeltaSCSet.mono hB1_kappa0 hC1_le
    · -- Sector 2: B_ring0 = -B2, reflection → constant 2*C_B2
      dsimp only [B_ring0, sectorRingBaseSet]
      have h_r := isProductLikeRealDeltaSCSet_reflect hδ_dyadic hδ_pos hB2_grid hB2_kappa0
      exact IsDeltaSCSet.mono h_r hC2_absorb
    · -- Sector 3: B_ring0 = -B1, reflection → constant 2*C_B1
      dsimp only [B_ring0, sectorRingBaseSet]
      have h_r := isProductLikeRealDeltaSCSet_reflect hδ_dyadic hδ_pos hB1_grid hB1_kappa0
      exact IsDeltaSCSet.mono h_r hC1_absorb

  -- Goal 3: size lower
  have h_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B_ring0 := by
    fin_cases sector_idx
    · dsimp only [B_ring0, sectorRingBaseSet]; exact hB2_lower
    · dsimp only [B_ring0, sectorRingBaseSet]; exact hB1_lower
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB2_intgrid hB2_bdd]; exact hB2_lower
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB1_intgrid hB1_bdd]; exact hB1_lower

  -- Goal 4: size upper
  have h_upper : Nreal δ B_ring0 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    fin_cases sector_idx
    · dsimp only [B_ring0, sectorRingBaseSet]; exact hB2_upper
    · dsimp only [B_ring0, sectorRingBaseSet]; exact hB1_upper
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB2_intgrid hB2_bdd]; exact hB2_upper
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [nreal_reflection_eq hδ_pos hB1_intgrid hB1_bdd]; exact hB1_upper

  -- Goal 5: self-diff bound
  have h_self_diff : Nreal δ (Set.image2 (· - ·) B_ring0 B_ring0) ≤
      ENNReal.ofReal K_work * Nreal δ B_ring0 := by
    fin_cases sector_idx
    · dsimp only [B_ring0, sectorRingBaseSet]; exact h_diff_B2B2
    · dsimp only [B_ring0, sectorRingBaseSet]; exact h_diff_B1B1
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [neg_diff_eq hδ_pos hB2_intgrid hB2_bdd,
          nreal_reflection_eq hδ_pos hB2_intgrid hB2_bdd]
      exact h_diff_B2B2
    · dsimp only [B_ring0, sectorRingBaseSet]
      rw [neg_diff_eq hδ_pos hB1_intgrid hB1_bdd,
          nreal_reflection_eq hδ_pos hB1_intgrid hB1_bdd]
      exact h_diff_B1B1

  -- Goal 6: cross-diff bound
  have h_cross_diff : Nreal δ (Set.image2 (· - ·) B_coord B_ring0) ≤
      ENNReal.ofReal K_work * Nreal δ B_ring0 := by
    fin_cases sector_idx
    · -- Sector 0: B_coord = B1, B_ring0 = B2
      dsimp only [B_coord, B_ring0, sectorCoordSet, sectorRingBaseSet]
      rw [cross_neg_eq hδ_pos hB2_intgrid hB1_intgrid hB2_bdd hB1_bdd]
      exact h_diff_B2B1_over_B2
    · -- Sector 1: B_coord = B2, B_ring0 = B1
      dsimp only [B_coord, B_ring0, sectorCoordSet, sectorRingBaseSet]
      exact h_diff_B2B1_over_B1
    · -- Sector 2: B_coord = B1, B_ring0 = -B2
      dsimp only [B_coord, B_ring0, sectorCoordSet, sectorRingBaseSet]
      rw [diff_neg_eq_add, nreal_reflection_eq hδ_pos hB2_intgrid hB2_bdd]
      exact h_sum_B1B2_over_B2
    · -- Sector 3: B_coord = B2, B_ring0 = -B1
      dsimp only [B_coord, B_ring0, sectorCoordSet, sectorRingBaseSet]
      have h_comm : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
        ext z; simp [Set.mem_image2, add_comm] <;> constructor <;>
          rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, by ring⟩
      rw [diff_neg_eq_add, h_comm, nreal_reflection_eq hδ_pos hB1_intgrid hB1_bdd]
      exact h_sum_B1B2_over_B1

  -- Goal 9: graph subset
  have h_product_eq : sectorProductSet sector_idx B1 B2 = B_ring0 ×ˢ B_coord := by
    exact sectorProductSet_eq sector_idx B1 B2
  have hG_subset : G ⊆ B_ring0 ×ˢ B_coord := by
    rw [←h_product_eq]; exact hG_sector

  exact ⟨B_ring0, B_coord, c, h_translate_subset, h_delta, h_lower, h_upper,
    h_self_diff, h_cross_diff, rfl, rfl, hG_subset⟩

/-- Extract all four-sector regularity, size, and difference bounds from
phase56 B1/B2 data.

This is a convenience wrapper around `phase8_sector_translation_main` that
drops the graph-subset output and produces the four families of bounds
required by `direction_failure_composition_v6`:

- `h_diff1_sector`: self-difference bound for `sectorRingBaseSet i`
- `h_diff2_sector`: cross-difference bound for `sectorCoordSet i - sectorRingBaseSet i`
- `h_size_upper_sector`: upper covering-number bound
- `hB1_delta_kappa_sector`: delta-set regularity

All four are uniform in `i : Fin 4`.
-/
lemma four_sector_bounds
    {δ s κ0 εnc C_B1 C_B2 K_work : ℝ}
    {B1 B2 : Set ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hB1_grid : B1 ⊆ productLikeUnitGrid δ)
    (hB2_grid : B2 ⊆ productLikeUnitGrid δ)
    (hB1_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 C_B1 B1)
    (hB2_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 C_B2 B2)
    (hB1_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B1)
    (hB1_upper : Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB2_lower : ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B2)
    (hB2_upper : Nreal δ B2 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hC1_absorb : 2 * C_B1 ≤ K_work * δ ^ (-εnc))
    (hC2_absorb : 2 * C_B2 ≤ K_work * δ ^ (-εnc))
    (h_diff_B1B1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_diff_B2B2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_work * Nreal δ B2)
    (h_diff_B2B1_over_B1 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_diff_B2B1_over_B2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_work * Nreal δ B2)
    (h_sum_B1B2_over_B1 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_work * Nreal δ B1)
    (h_sum_B1B2_over_B2 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_work * Nreal δ B2) :
    (∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorRingBaseSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_work * Nreal δ (sectorRingBaseSet i B1 B2)) ∧
    (∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorCoordSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_work * Nreal δ (sectorRingBaseSet i B1 B2)) ∧
    (∀ i : Fin 4,
      Nreal δ (sectorRingBaseSet i B1 B2) ≤
        ENNReal.ofReal (K_work * δ ^ (-(s + εnc)))) ∧
    (∀ i : Fin 4,
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) (sectorRingBaseSet i B1 B2)) := by
  have h_all : ∀ (i : Fin 4),
      ∃ (B_ring0 B_coord : Set ℝ) (c : ℤ),
        ProductReduction.translateSet (c : ℝ) B_ring0 ⊆ Set.Icc (1 : ℝ) 2 ∧
        IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) B_ring0 ∧
        ENNReal.ofReal (δ ^ (-(s - εnc))) ≤ Nreal δ B_ring0 ∧
        Nreal δ B_ring0 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) ∧
        Nreal δ (Set.image2 (· - ·) B_ring0 B_ring0) ≤ ENNReal.ofReal K_work * Nreal δ B_ring0 ∧
        Nreal δ (Set.image2 (· - ·) B_coord B_ring0) ≤ ENNReal.ofReal K_work * Nreal δ B_ring0 ∧
        B_ring0 = sectorRingBaseSet i B1 B2 ∧
        B_coord = sectorCoordSet i B1 B2 ∧
        (∅ : Set (ℝ × ℝ)) ⊆ B_ring0 ×ˢ B_coord := by
    intro i
    exact phase8_sector_translation_main i hδ_pos hδ_dyadic hB1_grid hB2_grid
      hB1_kappa0 hB2_kappa0 hB1_lower hB1_upper hB2_lower hB2_upper
      hC1_absorb hC2_absorb h_diff_B1B1 h_diff_B2B2 h_diff_B2B1_over_B1 h_diff_B2B1_over_B2
      h_sum_B1B2_over_B1 h_sum_B1B2_over_B2 (G := (∅ : Set (ℝ × ℝ))) (by simp)
  have h1 : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorRingBaseSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_work * Nreal δ (sectorRingBaseSet i B1 B2) := by
    intro i
    rcases h_all i with ⟨B_ring0, B_coord, c, _h_trans, _h_delta, _h_lower, _h_upper, h_self_diff, _h_cross_diff, h_eq, _h_eq2, _hG⟩
    simpa [h_eq] using h_self_diff
  have h2 : ∀ i : Fin 4,
      Nreal δ (Set.image2 (· - ·) (sectorCoordSet i B1 B2) (sectorRingBaseSet i B1 B2)) ≤
        ENNReal.ofReal K_work * Nreal δ (sectorRingBaseSet i B1 B2) := by
    intro i
    rcases h_all i with ⟨B_ring0, B_coord, c, _h_trans, _h_delta, _h_lower, _h_upper, _h_self_diff, h_cross_diff, h_eq1, h_eq2, _hG⟩
    simpa [h_eq1, h_eq2] using h_cross_diff
  have h3 : ∀ i : Fin 4,
      Nreal δ (sectorRingBaseSet i B1 B2) ≤
        ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
    intro i
    rcases h_all i with ⟨B_ring0, _B_coord, _c, _h_trans, _h_delta, _h_lower, h_upper, _h_self_diff, _h_cross_diff, h_eq, _h_eq2, _hG⟩
    simpa [h_eq] using h_upper
  have h4 : ∀ i : Fin 4,
      IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) (sectorRingBaseSet i B1 B2) := by
    intro i
    rcases h_all i with ⟨B_ring0, _B_coord, _c, _h_trans, h_delta, _h_lower, _h_upper, _h_self_diff, _h_cross_diff, h_eq, _h_eq2, _hG⟩
    simpa [h_eq] using h_delta
  exact ⟨h1, h2, h3, h4⟩

end ProductLikeIncidence
