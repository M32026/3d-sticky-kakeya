import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Global AD via cell decomposition

This module states the infrastructure for constructing global AD on horizontal
slices from local AD on balls, using a grid-cell decomposition.

## Mechanism

1. The cubical shading decomposes the configuration into grid cubes of side `delta`.
2. Each horizontal slice intersects cells that are squares of side `delta`.
3. Each cell has diameter `delta * √2 ≤ √delta` (for `delta ≤ 1/2`), so it fits
   inside the local AD ball `B(p, √delta)`.
4. Per-cell local AD is obtained by restricting the local AD to the cell.
5. Per-cell direction transfer converts AD from the plane-map direction to the
   global grain direction (constant factor `100 * C` per cell).
6. The per-cell AD bounds are combined via union stability.

## Open issues

- The per-cell direction transfer from `planeMap(p)` to the global direction
  requires showing the plane-map normal (or its Householder reflection) satisfies
  `|n0| ≥ 1/3` and `|n2| ≤ 1/10`.
- The final constant must match the output `C`. The loss increase from cell
  counting must be absorbed by the two-stage loss structure in `FromCritical`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-!
## 1. Per-cell direction transfer

For a cell contained in a δ×δ square at fixed height, the projection in ANY
direction has bounded length. With |slope| ≤ 3/√2, the projection length is
at most 4δ. Hence the covering number at scale ρ ≥ δ is at most 4, which is
≤ 100*C (since C ≥ 1). This makes the per-cell direction transfer trivial.
-/

/-- Per-cell direction transfer: a small grid cell has AD in ANY direction.

The projection of a δ×δ cell onto direction `(1, slope, 0)` has length at most
`δ * (1 + |slope|)`. With `|slope| ≤ 3/√2`, this is ≤ 4δ. Thus the covering
number at any scale ρ ≥ δ is at most 4, and the AD bound `100*C ≥ 100 ≥ 4`
holds trivially. -/
lemma per_cell_direction_transfer
    {delta sigma : ℝ} {C : ENNReal}
    {E : Set Point3} {z slope : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hE_height : ∀ p ∈ E, p 2 = z)
    (a b : ℝ)
    (hE_rect : E ⊆ {p | p 2 = z ∧ a ≤ p 0 ∧ p 0 ≤ a + delta ∧ b ≤ p 1 ∧ p 1 ≤ b + delta})
    (hslope_bound : |slope| ≤ 3) :
    PureWZ2PaperADSet1
      (scalarProjection (globalGrainDirection slope) E)
      delta (1 - sigma) (100 * C) := by
  let d := globalGrainDirection slope
  let S := scalarProjection d E
  let c : ℝ := a + slope * b
  let r : ℝ := delta * (1 + |slope|)
  have hr_pos : 0 ≤ r := by positivity
  have hS_sub : S ⊆ Set.Icc (c - r) (c + r) := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    have h2 : a ≤ p 0 := (hE_rect hp).2.1
    have h3 : p 0 ≤ a + delta := (hE_rect hp).2.2.1
    have h4 : b ≤ p 1 := (hE_rect hp).2.2.2.1
    have h5 : p 1 ≤ b + delta := (hE_rect hp).2.2.2.2
    have h6 : |(p 0 + slope * p 1) - c| ≤ r := by
      have h71 : a ≤ p 0 := h2
      have h72 : p 0 ≤ a + delta := h3
      have h73 : b ≤ p 1 := h4
      have h74 : p 1 ≤ b + delta := h5
      have h7 : |p 0 - a| ≤ delta := by
        have h75 : 0 ≤ p 0 - a := by linarith
        rw [abs_of_nonneg h75] <;> linarith
      have h8 : |p 1 - b| ≤ delta := by
        have h85 : 0 ≤ p 1 - b := by linarith
        rw [abs_of_nonneg h85] <;> linarith
      calc |(p 0 + slope * p 1) - (a + slope * b)|
        = |(p 0 - a) + slope * (p 1 - b)| := by ring_nf
      _ ≤ |p 0 - a| + |slope * (p 1 - b)| := by
        exact abs_add_le _ _
      _ = |p 0 - a| + |slope| * |p 1 - b| := by rw [abs_mul]
      _ ≤ delta + |slope| * delta := by
        have h9 : |slope| * |p 1 - b| ≤ |slope| * delta :=
          mul_le_mul_of_nonneg_left h8 (abs_nonneg slope)
        linarith
      _ = r := by simp [r] <;> ring
    have h_inner : inner ℝ p d = p 0 + slope * p 1 := by
      have h_d0 : d 0 = 1 := by
        simp [d, globalGrainDirection, EuclideanSpace.single_apply] <;> norm_num
      have h_d1 : d 1 = slope := by
        simp [d, globalGrainDirection, EuclideanSpace.single_apply] <;> ring
      have h_d2 : d 2 = 0 := by
        simp [d, globalGrainDirection, EuclideanSpace.single_apply] <;> norm_num
      have h : inner ℝ p d = p 0 * d 0 + p 1 * d 1 + p 2 * d 2 := by
        simp [PiLp.inner_apply, Fin.sum_univ_succ]
        <;> ring
      rw [h, h_d0, h_d1, h_d2] <;> ring
    have h9 : c - r ≤ inner ℝ p d := by
      rw [h_inner]
      linarith [abs_le.mp h6]
    have h10 : inner ℝ p d ≤ c + r := by
      rw [h_inner]
      linarith [abs_le.mp h6]
    exact ⟨h9, h10⟩
  have hr_le_4delta : r ≤ 4 * delta := by
    have h9 : |slope| ≤ 3 := hslope_bound
    calc r = delta * (1 + |slope|) := by rfl
      _ ≤ delta * (1 + 3) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * delta := by ring
  have hC100_one : (1 : ENNReal) ≤ 100 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (100 : ENNReal) ≤ 100 * C := le_mul_of_one_le_right' h1
    have h3 : (1 : ENNReal) ≤ 100 := by norm_num
    exact h3.trans h2
  have hC100_top : (100 * C) ≠ ⊤ := by
    intro h; have h4 : C = ⊤ := by simpa [ENNReal.mul_eq_top] using h
    exact hC_top h4
  refine ⟨hdelta, by linarith, by linarith, hC100_one, hC100_top, ?_⟩
  intro rho hrho hdelta_rho left length hlen
  have h_rho_pos : 0 < rho := by linarith
  have hr_le_4rho : r ≤ 4 * rho := by
    calc r ≤ 4 * delta := hr_le_4delta
      _ ≤ 4 * rho := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  let coverF : Finset ℝ := {c - 3 * rho, c - rho, c + rho, c + 3 * rho}
  let cover : Set ℝ := (coverF : Set ℝ)
  have hcover : Metric.IsCover ⟨rho, hrho⟩ S cover := by
    intro x hx
    have hxin : x ∈ Set.Icc (c - r) (c + r) := hS_sub hx
    have hxl : c - r ≤ x := hxin.1
    have hxr : x ≤ c + r := hxin.2
    by_cases h10 : x ≤ c
    · by_cases h11 : x ≤ c - 2 * rho
      · refine ⟨c - 3 * rho, by simp [cover, coverF], ?_⟩
        have h12 : |x - (c - 3 * rho)| ≤ rho := by
          have h13 : c - 4 * rho ≤ x := by linarith [hr_le_4rho]
          rw [abs_le] <;> constructor <;> linarith
        exact_mod_cast h12
      · refine ⟨c - rho, by simp [cover, coverF], ?_⟩
        have h12 : |x - (c - rho)| ≤ rho := by
          have h13 : c - 2 * rho < x := by linarith
          rw [abs_le] <;> constructor <;> linarith
        exact_mod_cast h12
    · by_cases h11 : c + 2 * rho ≤ x
      · refine ⟨c + 3 * rho, by simp [cover, coverF], ?_⟩
        have h12 : |x - (c + 3 * rho)| ≤ rho := by
          have h14 : x ≤ c + 4 * rho := by linarith [hr_le_4rho]
          rw [abs_le] <;> constructor <;> linarith
        exact_mod_cast h12
      · refine ⟨c + rho, by simp [cover, coverF], ?_⟩
        have h12 : |x - (c + rho)| ≤ rho := by
          have h13 : c < x := by linarith
          have h14 : x < c + 2 * rho := by linarith
          rw [abs_le] <;> constructor <;> linarith
        exact_mod_cast h12
  have h_card : coverF.card = 4 := by
    have hpos : 0 < rho := h_rho_pos
    have hne1 : c + rho ≠ c + 3 * rho := by linarith
    have hne2 : c - rho ≠ c + rho := by linarith
    have hne3 : c - rho ≠ c + 3 * rho := by linarith
    have hne4 : c - 3 * rho ≠ c - rho := by linarith
    have hne5 : c - 3 * rho ≠ c + rho := by linarith
    have hne6 : c - 3 * rho ≠ c + 3 * rho := by linarith
    have h9 : (c + rho) ∉ ({c + 3 * rho} : Finset ℝ) := by
      simp [hne1]
    have h10 : (c - rho) ∉ ({c + rho, c + 3 * rho} : Finset ℝ) := by
      simp [hne2, hne3] <;> tauto
    have h11 : (c - 3 * rho) ∉ ({c - rho, c + rho, c + 3 * rho} : Finset ℝ) := by
      simp [hne4, hne5, hne6] <;> tauto
    have h_eq : coverF = insert (c - 3 * rho) (insert (c - rho) (insert (c + rho) ({c + 3 * rho} : Finset ℝ))) := by
      ext x; simp [coverF] <;> tauto
    rw [h_eq]
    have h14 : (insert (c - 3 * rho) (insert (c - rho) (insert (c + rho) ({c + 3 * rho} : Finset ℝ)))).card = 4 := by
      rw [Finset.card_insert_of_notMem h11, Finset.card_insert_of_notMem h10,
        Finset.card_insert_of_notMem h9, Finset.card_singleton]
      <;> norm_num
    exact h14
  have h10 : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤ (4 : ENNReal) := by
    have h11 : Metric.externalCoveringNumber ⟨rho, hrho⟩ S ≤ cover.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover
    have h13 : cover.encard = (coverF.card : ℕ∞) := by
      simp [cover, Set.encard]
      <;> rfl
    rw [h13] at h11
    rw [h_card] at h11
    exact_mod_cast h11
  have h14 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) (1 - sigma) := by
    have h15 : 1 ≤ length / rho := by
      calc (1 : ℝ) = rho / rho := by field_simp [h_rho_pos.ne'] <;> ring
           _ ≤ length / rho := by gcongr
    have h16 : (1 : ℝ) ≤ Real.rpow (length / rho) (1 - sigma) :=
      Real.one_le_rpow h15 (by linarith)
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h16
  have h100 : (100 : ENNReal) ≤ 100 * C := by
    have h101 : (1 : ENNReal) ≤ C := hC_one
    have h102 : (100 : ENNReal) * (1 : ENNReal) ≤ (100 : ENNReal) * C := by gcongr
    simpa using h102
  have h15 : (100 * C) ≤ (100 * C) * Kakeya.realRpowENN (length / rho) (1 - sigma) :=
    le_mul_of_one_le_right' h14
  have h13 : (4 : ENNReal) ≤ (100 * C) * Kakeya.realRpowENN (length / rho) (1 - sigma) := by
    calc (4 : ENNReal)
      ≤ (100 : ENNReal) := by norm_num
    _ ≤ 100 * C := h100
    _ ≤ (100 * C) * Kakeya.realRpowENN (length / rho) (1 - sigma) := h15
  have h10' : (Metric.externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Set.Icc left (left + length)) : ENNReal) ≤
      (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) := by
    have h_sub : S ∩ Set.Icc left (left + length) ⊆ S := by
      intro x hx; exact hx.1
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
  exact h10'.trans (h10.trans h13)

/-!
## 2. Union stability for PureWZ2PaperADSet1
-/

/-- `PureWZ2PaperADSet1` is stable under finite unions with constant addition. -/
lemma PureWZ2PaperADSet1.union'
    {S T : Set ℝ} {delta alpha : ℝ} {C C' : ENNReal}
    (hS : PureWZ2PaperADSet1 S delta alpha C)
    (hT : PureWZ2PaperADSet1 T delta alpha C') :
    PureWZ2PaperADSet1 (S ∪ T) delta alpha (C + C') := by
  rcases hS with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hT with ⟨_, _, _, h4', h5', h7⟩
  have hC_top : (C + C') ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h5, h5'⟩
  refine ⟨h1, h2, h3, le_trans h4 (by simp), hC_top, ?_⟩
  intro rho hrho hdelta left length hlen
  have h_inter : (S ∪ T) ∩ Set.Icc left (left + length) =
        (S ∩ Set.Icc left (left + length)) ∪ (T ∩ Set.Icc left (left + length)) := by
    ext x; simp [Set.mem_union] <;> tauto
  rw [h_inter]
  let ε : NNReal := ⟨rho, hrho⟩
  let A := S ∩ Set.Icc left (left + length)
  let B := T ∩ Set.Icc left (left + length)
  have h8 : (Metric.externalCoveringNumber ε (A ∪ B) : ENNReal) ≤
        (Metric.externalCoveringNumber ε A : ENNReal) +
        (Metric.externalCoveringNumber ε B : ENNReal) := by
    exact_mod_cast externalCoveringNumber_union_le (ε := ε) (A := A) (B := B)
  have h9 := h6 rho hrho hdelta left length hlen
  have h10 := h7 rho hrho hdelta left length hlen
  calc _
    ≤ _ + _ := h8
  _ ≤ C * Kakeya.realRpowENN (length / rho) alpha +
        C' * Kakeya.realRpowENN (length / rho) alpha := by gcongr
  _ = (C + C') * Kakeya.realRpowENN (length / rho) alpha := by
    rw [add_mul]

/-- Finite union stability: if each set has AD with constant `K`,
    their indexed union has AD with constant `(s.card + 1) * K`.

    The `+1` handles the empty case (constant must be `≥ 1`). -/
lemma PureWZ2PaperADSet1.finset_biUnion
    {ι : Type*} {s : Finset ι} {f : ι → Set ℝ}
    {delta alpha : ℝ} {K : ENNReal}
    (hdelta : 0 < delta) (halpha : 0 < alpha) (halpha_one : alpha ≤ 1)
    (hK_one : 1 ≤ K) (hK_top : K ≠ ⊤)
    (h : ∀ i ∈ s, PureWZ2PaperADSet1 (f i) delta alpha K) :
    PureWZ2PaperADSet1 {x | ∃ i ∈ s, x ∈ f i} delta alpha
      ((↑s.card + 1 : ENNReal) * K) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h_empty : PureWZ2PaperADSet1 (∅ : Set ℝ) delta alpha K := by
      refine ⟨hdelta, halpha, halpha_one, hK_one, hK_top, ?_⟩
      intro rho hrho _ left length hlen
      have h_inter_empty : (∅ : Set ℝ) ∩ Set.Icc left (left + length) = (∅ : Set ℝ) := by simp
      have h_cover : (Metric.externalCoveringNumber ⟨rho, hrho⟩ ((∅ : Set ℝ) ∩ Set.Icc left (left + length)) : ENNReal) = 0 := by
        rw [h_inter_empty, Metric.externalCoveringNumber_empty]
        <;> simp
      rw [h_cover]
      <;> simp
    have h_set : {x | ∃ i ∈ (∅ : Finset ι), x ∈ f i} = (∅ : Set ℝ) := by
      ext x; simp
    rw [h_set]
    have h_card_empty : ((↑(∅ : Finset ι).card + 1 : ENNReal) * K) = K := by
      simp
    rw [h_card_empty]
    exact h_empty
  | @insert i s hi ih =>
    have h1 : PureWZ2PaperADSet1 (f i) delta alpha K :=
      h i (Finset.mem_insert_self i s)
    have h2 : PureWZ2PaperADSet1 {x | ∃ j ∈ s, x ∈ f j} delta alpha
        ((↑s.card + 1 : ENNReal) * K) :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h3 := h1.union' h2
    have h_union : {x | ∃ k ∈ insert i s, x ∈ f k} =
        f i ∪ {x | ∃ j ∈ s, x ∈ f j} := by
      ext x
      simp only [Finset.mem_insert, Set.mem_union, Set.mem_setOf_eq]
      <;> aesop
    have h_card : (↑(insert i s).card : ENNReal) = (↑s.card : ENNReal) + 1 := by
      rw [Finset.card_insert_of_notMem hi] <;> simp
    have h_const : ((↑(insert i s).card + 1 : ENNReal) * K) =
        K + ((↑s.card + 1 : ENNReal) * K) := by
      rw [h_card]
      simp [add_mul, one_mul, add_assoc] <;> ring
    rw [h_union, h_const]
    exact h3

/-!
## 3. Main cell-decomposition theorem

Given a finite cover of a height-z set by δ×δ grid cells, each cell's projection
in any direction has trivial AD (covering number ≤ 4) because its diameter is
at most 4δ. Combining via finite union stability yields global AD with constant
`(N + 1) * 100 * C` where `N` is the number of cells.
-/

/-- Global AD from a finite δ×δ cell cover.

Each cell rectangle `[a, a+δ] × [b, b+δ]` at height `z` has projection length
at most `δ * (1 + |slope|) ≤ 4δ`, so its covering number at any scale `ρ ≥ δ`
is at most 4. With `C ≥ 1`, the per-cell AD constant `100 * C` dominates.
The finite union of `N` such cells has AD constant `(N + 1) * 100 * C`. -/
theorem global_ad_via_cell_decomposition
    {ι : Type*} {delta sigma : ℝ} {C : ENNReal} {E : Set Point3} {z slope : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hE_height : ∀ p ∈ E, p 2 = z)
    (hslope_bound : |slope| ≤ 3)
    (cells : Finset ι)
    (cellLowerLeft : ι → ℝ × ℝ)
    (cellRect : ι → Set Point3)
    (hcell : ∀ i ∈ cells, cellRect i ⊆
        {p | p 2 = z ∧ (cellLowerLeft i).1 ≤ p 0 ∧ p 0 ≤ (cellLowerLeft i).1 + delta ∧
                       (cellLowerLeft i).2 ≤ p 1 ∧ p 1 ≤ (cellLowerLeft i).2 + delta})
    (hcover : E ⊆ {p | ∃ i ∈ cells, p ∈ cellRect i}) :
    PureWZ2PaperADSet1
      (scalarProjection (globalGrainDirection slope) E)
      delta (1 - sigma)
      ((↑cells.card + 1 : ENNReal) * 100 * C) := by
  let d := globalGrainDirection slope
  let K : ENNReal := 100 * C
  have hK_one : (1 : ENNReal) ≤ K := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (100 : ENNReal) ≤ 100 * C := le_mul_of_one_le_right' h1
    have h3 : (1 : ENNReal) ≤ 100 := by norm_num
    exact h3.trans h2
  have hK_top : K ≠ ⊤ := by
    intro h; have h4 : C = ⊤ := by simpa [K, ENNReal.mul_eq_top] using h
    exact hC_top h4
  let E_cell (i : ι) : Set Point3 := E ∩ cellRect i
  have h_per_cell : ∀ i ∈ cells,
      PureWZ2PaperADSet1 (scalarProjection d (E_cell i)) delta (1 - sigma) K := by
    intro i hi
    let ab := cellLowerLeft i
    have h_height : ∀ p ∈ E_cell i, p 2 = z := by
      intro p hp; exact hE_height p hp.1
    have h_rect : E_cell i ⊆ {p | p 2 = z ∧ ab.1 ≤ p 0 ∧ p 0 ≤ ab.1 + delta ∧
        ab.2 ≤ p 1 ∧ p 1 ≤ ab.2 + delta} := by
      intro p hp; exact hcell i hi hp.2
    exact per_cell_direction_transfer hdelta hsigma hsigma_one hC_one hC_top
      h_height ab.1 ab.2 h_rect hslope_bound
  let f (i : ι) : Set ℝ := scalarProjection d (E_cell i)
  have halpha : 0 < (1 - sigma) := by linarith
  have halpha_one : (1 - sigma) ≤ 1 := by linarith
  have h_union_ad : PureWZ2PaperADSet1 {x | ∃ i ∈ cells, x ∈ f i}
      delta (1 - sigma) ((↑cells.card + 1 : ENNReal) * K) :=
    PureWZ2PaperADSet1.finset_biUnion hdelta halpha halpha_one hK_one hK_top h_per_cell
  have h_sub : scalarProjection d E ⊆ {x | ∃ i ∈ cells, x ∈ f i} := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    have h_p_in_union : p ∈ {p | ∃ i ∈ cells, p ∈ cellRect i} := hcover hp
    rcases h_p_in_union with ⟨i, hi, h_p_in_rect⟩
    have h_p_in_E_cell : p ∈ E_cell i := ⟨hp, h_p_in_rect⟩
    exact ⟨i, hi, ⟨p, h_p_in_E_cell, rfl⟩⟩
  have h_result := h_union_ad.mono_set h_sub
  have h_assoc : ((↑cells.card + 1 : ENNReal) * (100 * C)) =
        ((↑cells.card + 1 : ENNReal) * 100 * C) := by
    rw [mul_assoc]
  rw [h_assoc] at h_result
  exact h_result

/-!
## 4. Loss-adjustment and bounded-slice helpers
-/

/-- Weaken an AD bound from a smaller loss to a larger loss.

For `0 < loss1 ≤ loss2` and `0 < δ ≤ 1`, we have `δ^(-loss1) ≤ δ^(-loss2)`,
so `mono_const` gives the result. -/
lemma PureWZ2PaperADSet1.loss_weaken
    {S : Set ℝ} {delta alpha : ℝ} {loss1 loss2 : ℝ}
    (hAD : PureWZ2PaperADSet1 S delta alpha (Kakeya.realRpowENN delta (-loss1)))
    (h1 : 0 < loss1) (h2 : loss1 ≤ loss2)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    PureWZ2PaperADSet1 S delta alpha (Kakeya.realRpowENN delta (-loss2)) := by
  have hineq : Kakeya.realRpowENN delta (-loss1) ≤ Kakeya.realRpowENN delta (-loss2) := by
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    have h3 : -loss2 ≤ -loss1 := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h3
  have htop : Kakeya.realRpowENN delta (-loss2) ≠ ⊤ := by
    simp [Kakeya.realRpowENN] <;> positivity
  exact hAD.mono_const hineq htop

/-- Global AD for a bounded horizontal slice in `[-1,1]^2`.

Constructs a finite `δ×δ` grid cover and applies `global_ad_via_cell_decomposition`.
Outputs an existential AD constant `K` of the form `(N+1) * 100 * C`. -/
theorem bounded_slice_global_ad
    {delta sigma : ℝ} {C : ENNReal} {E : Set Point3} {z slope : ℝ}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hE_height : ∀ p ∈ E, p 2 = z)
    (hE_bounded : E ⊆ {p | p 2 = z ∧ -1 ≤ p 0 ∧ p 0 ≤ 1 ∧ -1 ≤ p 1 ∧ p 1 ≤ 1})
    (hslope_bound : |slope| ≤ 3) :
    ∃ (K : ENNReal), K ≠ ⊤ ∧
      PureWZ2PaperADSet1 (scalarProjection (globalGrainDirection slope) E)
        delta (1 - sigma) K := by
  classical
  let n : ℤ := ⌈1 / delta⌉ + 1
  let cells : Finset (ℤ × ℤ) := Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n
  let cellLowerLeft (ij : ℤ × ℤ) : ℝ × ℝ :=
    (delta * (ij.1 : ℝ), delta * (ij.2 : ℝ))
  let cellRect (ij : ℤ × ℤ) : Set Point3 :=
    {p | p 2 = z ∧
      delta * (ij.1 : ℝ) ≤ p 0 ∧ p 0 ≤ delta * ((ij.1 : ℝ) + 1) ∧
      delta * (ij.2 : ℝ) ≤ p 1 ∧ p 1 ≤ delta * ((ij.2 : ℝ) + 1)}

  have hcell : ∀ (ij : ℤ × ℤ), ij ∈ cells → cellRect ij ⊆
      {p | p 2 = z ∧ (cellLowerLeft ij).1 ≤ p 0 ∧ p 0 ≤ (cellLowerLeft ij).1 + delta ∧
           (cellLowerLeft ij).2 ≤ p 1 ∧ p 1 ≤ (cellLowerLeft ij).2 + delta} := by
    intro ij _ p hp
    have h1 : p 2 = z := hp.1
    have h2 : delta * (ij.1 : ℝ) ≤ p 0 := hp.2.1
    have h3 : p 0 ≤ delta * ((ij.1 : ℝ) + 1) := hp.2.2.1
    have h4 : delta * (ij.2 : ℝ) ≤ p 1 := hp.2.2.2.1
    have h5 : p 1 ≤ delta * ((ij.2 : ℝ) + 1) := hp.2.2.2.2
    have h3' : p 0 ≤ (cellLowerLeft ij).1 + delta := by
      have h_eq : (cellLowerLeft ij).1 + delta = delta * ((ij.1 : ℝ) + 1) := by
        simp [cellLowerLeft] <;> ring
      rw [h_eq]; exact h3
    have h5' : p 1 ≤ (cellLowerLeft ij).2 + delta := by
      have h_eq : (cellLowerLeft ij).2 + delta = delta * ((ij.2 : ℝ) + 1) := by
        simp [cellLowerLeft] <;> ring
      rw [h_eq]; exact h5
    exact ⟨h1, h2, h3', h4, h5'⟩

  have h_i_range (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
      ∃ (i : ℤ), -n ≤ i ∧ i ≤ n ∧ delta * (i : ℝ) ≤ x ∧ x < delta * ((i : ℝ) + 1) := by
    let i : ℤ := ⌊x / delta⌋
    have h1 : delta * (i : ℝ) ≤ x := by
      have h11 : (i : ℝ) ≤ x / delta := Int.floor_le (x / delta)
      have h : delta * (i : ℝ) ≤ delta * (x / delta) := by gcongr
      have h2 : delta * (x / delta) = x := by
        field_simp [hdelta.ne'] <;> ring
      rw [h2] at h; exact h
    have h2 : x < delta * ((i : ℝ) + 1) := by
      have h21 : x / delta < (i : ℝ) + 1 := Int.lt_floor_add_one (x / delta)
      have h : delta * (x / delta) < delta * ((i : ℝ) + 1) := by gcongr
      have h22 : delta * (x / delta) = x := by
        field_simp [hdelta.ne'] <;> ring
      rw [h22] at h; exact h
    have h3 : -n ≤ i := by
      have h31 : x / delta ≥ -1 / delta := by gcongr
      have h32 : ⌊x / delta⌋ ≥ ⌊-1 / delta⌋ := Int.floor_mono h31
      have h33 : ⌊-1 / delta⌋ = -⌈1 / delta⌉ := by
        rw [show (-1 / delta : ℝ) = -(1 / delta) by ring]
        rw [Int.floor_neg]
      rw [h33] at h32
      simp only [n, sub_eq_add_neg] at * <;> linarith
    have h4 : i ≤ n := by
      have h41 : x / delta ≤ 1 / delta := by gcongr
      have h42 : ⌊x / delta⌋ ≤ ⌊1 / delta⌋ := Int.floor_mono h41
      have h43 : ⌊1 / delta⌋ ≤ ⌈1 / delta⌉ := Int.floor_le_ceil (1 / delta)
      simp only [n] at * <;> linarith
    exact ⟨i, h3, h4, h1, h2⟩

  have hcover : E ⊆ {p | ∃ (ij : ℤ × ℤ), ij ∈ cells ∧ p ∈ cellRect ij} := by
    intro p hp
    have h_b : p 2 = z ∧ -1 ≤ p 0 ∧ p 0 ≤ 1 ∧ -1 ≤ p 1 ∧ p 1 ≤ 1 := hE_bounded hp
    rcases h_i_range (p 0) h_b.2.1 h_b.2.2.1 with ⟨i, hi_low, hi_high, hi1, hi2⟩
    rcases h_i_range (p 1) h_b.2.2.2.1 h_b.2.2.2.2 with ⟨j, hj_low, hj_high, hj1, hj2⟩
    have hi_in : i ∈ Finset.Icc (-n) n := by
      simp only [Finset.mem_Icc]; exact ⟨hi_low, hi_high⟩
    have hj_in : j ∈ Finset.Icc (-n) n := by
      simp only [Finset.mem_Icc]; exact ⟨hj_low, hj_high⟩
    have hij_in : (i, j) ∈ cells := Finset.mem_product.mpr ⟨hi_in, hj_in⟩
    have h_p_in_rect : p ∈ cellRect (i, j) := by
      simp only [cellRect, Set.mem_setOf_eq]
      exact ⟨h_b.1, hi1, by linarith, hj1, by linarith⟩
    exact ⟨(i, j), hij_in, h_p_in_rect⟩

  let K : ENNReal := (↑cells.card + 1) * 100 * C
  have hK_top : K ≠ ⊤ := by
    simp only [K]
    have h1 : (↑cells.card + 1 : ENNReal) ≠ ⊤ := by simp
    have h2 : (100 : ENNReal) ≠ ⊤ := by norm_num
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) hC_top

  have h_main : PureWZ2PaperADSet1 (scalarProjection (globalGrainDirection slope) E)
      delta (1 - sigma) K :=
    global_ad_via_cell_decomposition
      hdelta hsigma hsigma_one hC_one hC_top hE_height hslope_bound
      cells cellLowerLeft cellRect hcell hcover

  exact ⟨K, hK_top, h_main⟩

end Kakeya.Assouad

end
