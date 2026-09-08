/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.GapKatzTao

/-!
# The stopping time of GWZ Lemma 7.7(B)

The Katz–Tao half of the dividing-scales dichotomy.  This file is the `Δ_max` twin of the
Frostman stopping time in `Kakeya/MultiScaleFac/Stopping.lean`, and it reuses that file's
combinatorial skeleton `MultiScaleFac.exists_maximal_cuts_abstract` verbatim; only the tracked
quantity changes.

## The node convention

`Δ_max` is tracked on the **node** families of the uniform structure — the essentially distinct
`ρ`-tubes `𝕋_ρ` of GWZ Definition 2.1 — and never on the thickened family `𝕋^{(ρ)}` with its
leaf multiplicities.  This is forced, not a matter of taste:

* `StickyKakeya.card_mul_le_of_isKatzTaoAtEveryScale` below shows that the multiplicity-carrying
  reading — `Δ_max(𝕋^{(ρ)}) ≤ C` on the full index set `s`, already at `ρ = 1` — implies
  `#s ≲_n C`.  With `C = δ^{-o(1)}` that
  caps the family at `δ^{-o(1)}` tubes, whereas the families GWZ Lemma 7.7(B) is applied to have
  `≈ δ^{-(n-1)}` tubes.  So the multiplicity reading is unsatisfiable in the intended regime.
* The Wang–Zahl source states the definition for a *set* of `ρ`-tubes: "there exists `ρ` and a
  set of `ρ`-tubes `𝕋_ρ`" with "`𝕋_ρ` is a `K`-balanced partitioning cover of `𝕋`" and
  "`C_KT(𝕋_ρ) ≤ K`" (`blueprint/src/WZ2/250224e_K3.tex:4734`).

On the node families the quantity behaves as it should: for a Kakeya family the `ρ`-nodes number
`≈ ρ^{-(n-1)}` and each has volume `≈ ρ^{n-1}`, so `Δ_max ≈ 1` at every scale.

## The duality with Lemma 7.7(A)

The two stopping times are mirror images, and the mirror is the direction in which the tracked
quantity is inherited (blueprint `section7.tex`, the two inheritance principles):

* `C_F` passes to *coarse* families, so in (A) the coarse half of a cut is free — it is
  `MultiScaleFac.BlockRestrictStep` — and the stopping test must supply the **fine** half.
* `Δ_max` passes to *subfamilies*, so in (B) the fine half of a cut is free — it is
  `ConvexSpaceBody.IsKatzTao.subset` applied to the node index set, which shrinks with the
  anchor — and the stopping test must supply the **coarse** half.

Consequently (B) needs no analogue of `MultiScaleFac.BlockRestrictStep`, and no geometric constant
accumulates along the stopping time: where (A) carries `C' ^ N`, (B) carries the single constant
it starts with.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section Multiplicity

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}

end Multiplicity

section Blocks

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} {N : ℕ}

/-- **The per-anchor block bound of GWZ Lemma 7.7(B).**  `BlockKatzTaoAt u C ζ a b i₀` says that the
`σ_b`-nodes contained in the anchor `T_{i₀}^{(σ_a)}` are `C (σ_a/σ_b)^ζ`-Katz–Tao, where
`σ_k = gridScale δ N k`.  The uniformity witnesses are carried as a function `u`, supplied only on
the grid range `k ≤ N` since off it the requirement would be unsatisfiable; accordingly the bound is
stated as `∀ hb : b ≤ N, …`. -/
def BlockKatzTaoAt (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ζ : ℝ) (a b : ℕ) (i₀ : ι) : Prop :=
  ∀ hb : b ≤ N,
    ConvexSpaceBody.IsKatzTao (gapNodeIndexAtScale (u b hb) i₀ (5 * gridScale δ N a))
      (fun j => ((u b hb).parentTube j).toConvexSpaceBody)
      ((C : ENNReal) * ENNReal.ofReal
        (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ))

/-- **The block bound of GWZ Lemma 7.7(B)**, quantified over anchors.  This is the invariant the
stopping time maintains on every adjacent block of its cut set. -/
def BlockKatzTao (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
    (C : NNReal) (ζ : ℝ) (a b : ℕ) : Prop :=
  ∀ i₀ ∈ s, BlockKatzTaoAt u C ζ a b i₀

omit [Nontrivial E] in
/-- **The block bound weakens as the constant and the exponent grow.**  The ratio `σ_a/σ_b` is at
least `1` for `a ≤ b`, so raising the exponent enlarges the right-hand side.  This is the `hmono`
hypothesis of `MultiScaleFac.exists_maximal_cuts_abstract`. -/
theorem BlockKatzTaoAt.mono (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C C' : NNReal} {ζ ζ' : ℝ} (hCC' : C ≤ C') (_hζ : 0 ≤ ζ) (hζζ' : ζ ≤ ζ')
    {a b : ℕ} (hab : a ≤ b) {i₀ : ι} (h : BlockKatzTaoAt u C ζ a b i₀) :
    BlockKatzTaoAt u C' ζ' a b i₀ := by
  intro hb
  have hb_pos : 0 < (gridScale δ N b : ℝ) := by exact_mod_cast gridScale_pos hδ N b
  have hr1 : (1 : ℝ) ≤ (gridScale δ N a : ℝ) / (gridScale δ N b : ℝ) :=
    (one_le_div hb_pos).mpr (by exact_mod_cast gridScale_antitone hδ hδ1 N hab)
  exact (h hb).mono (mul_le_mul' (ENNReal.coe_le_coe.mpr hCC')
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hr1 hζζ')))

/-- **The exponent arithmetic of the fine half of a cut.**  The mirror of
`MultiScaleFac.gridScale_ratio_rpow_le_of_cut`: there the cut is measured from the coarse end and
the surviving ratio is `σ_a/σ_c`; here it is measured from the fine end (`c + ⌈ε(b-a)⌉ ≤ b`) and the
surviving ratio is `σ_c/σ_b`.  Both say a cut at relative depth `ε` leaves an `ε`-th power. -/
private theorem gridScale_ratio_rpow_le_of_cut_fine {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : (δ : ℝ) ≤ 1) (N : ℕ)
    {ε ζ ζ' : ℝ} (hεpos : 0 < ε) (hζ : 0 ≤ ζ) (hgap : ζ ≤ ε * ζ') {a c b : ℕ}
    (hac : a ≤ c) (hcb : c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b) :
    ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ
      ≤ ((gridScale δ N c : ℝ) / (gridScale δ N b : ℝ)) ^ ζ' := by
  by_cases hN0 : N = 0
  · subst N
    simp only [gridScale, Nat.cast_zero, div_zero, NNReal.rpow_zero, NNReal.coe_one, div_one,
      Real.one_rpow, le_refl]
  · have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
    have hratio_b : (gridScale δ N a : ℝ) / (gridScale δ N b : ℝ) =
        (δ : ℝ) ^ (-(((b : ℝ) - (a : ℝ)) / (N : ℝ))) := by
      rw [← NNReal.coe_div, gridScale_div_gridScale hδ N a b, NNReal.coe_rpow]
    have hratio_c : (gridScale δ N c : ℝ) / (gridScale δ N b : ℝ) =
        (δ : ℝ) ^ (-(((b : ℝ) - (c : ℝ)) / (N : ℝ))) := by
      rw [← NNReal.coe_div, gridScale_div_gridScale hδ N c b, NNReal.coe_rpow]
    rw [hratio_b, hratio_c, ← Real.rpow_mul hδpos.le, ← Real.rpow_mul hδpos.le]
    apply Real.rpow_le_rpow_of_exponent_ge hδpos hδ1
    have hbc0 : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast (by omega : a ≤ b))
    have hζ'0 : 0 ≤ ζ' :=
      nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hζ.trans hgap) hεpos
    have hεba_le_bc : ε * ((b : ℝ) - (a : ℝ)) ≤ (b : ℝ) - (c : ℝ) := by
      have h₁ : (c : ℝ) + (⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℝ) ≤ (b : ℝ) := by exact_mod_cast hcb
      linarith [Nat.le_ceil (ε * ((b : ℝ) - (a : ℝ)))]
    have hexp : ((b : ℝ) - (a : ℝ)) * ζ ≤ ((b : ℝ) - (c : ℝ)) * ζ' :=
      calc ((b : ℝ) - (a : ℝ)) * ζ ≤ ((b : ℝ) - (a : ℝ)) * (ε * ζ') :=
            mul_le_mul_of_nonneg_left hgap hbc0
        _ = ζ' * (ε * ((b : ℝ) - (a : ℝ))) := by ring
        _ ≤ ζ' * ((b : ℝ) - (c : ℝ)) := mul_le_mul_of_nonneg_left hεba_le_bc hζ'0
        _ = ((b : ℝ) - (c : ℝ)) * ζ' := mul_comm _ _
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
    rw [neg_mul, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right hNpos]
    exact hexp

omit [Nontrivial E] in
/-- **The fine half of a cut is free.**  Shrinking the anchor from `σ_a` to `σ_c` shrinks the node
index set while leaving the node bodies untouched, so the Katz–Tao bound passes to the smaller
family by `ConvexSpaceBody.IsKatzTao.subset`, still at the *parent's* right-hand side; the cut
margin `b - c ≥ ε(b-a)` with `ζ ≤ ε ζ'` converts that into the fine block's own right-hand side.
Unlike `MultiScaleFac.BlockRestrictStep` this costs no constant at all. -/
theorem BlockKatzTaoAt.anchor_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hεpos : 0 < ε)
    {u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu}
    {C : NNReal} {ζ ζ' : ℝ} (hζ : 0 ≤ ζ) (hgap : ζ ≤ ε * ζ') {a c b : ℕ} (hac : a ≤ c)
    (hcb : c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b) {i₀ : ι}
    (h : BlockKatzTaoAt u C ζ a b i₀) :
    BlockKatzTaoAt u C ζ' c b i₀ := by
  intro hb
  have hσca : gridScale δ N c ≤ gridScale δ N a := gridScale_antitone hδ hδ1 N hac
  have hsub : gapNodeIndexAtScale (u b hb) i₀ (5 * gridScale δ N c)
      ⊆ gapNodeIndexAtScale (u b hb) i₀ (5 * gridScale δ N a) := by
    have hrescale : ((T i₀).rescale (5 * gridScale δ N c)).toConvexSpaceBody
        ≤ ((T i₀).rescale (5 * gridScale δ N a)).toConvexSpaceBody :=
      Tube.rescale_le_rescale_of_radius_le (T i₀) (by gcongr)
    intro i hi
    simp only [gapNodeIndexAtScale, Kakeya.familyIn, Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans hrescale⟩
  exact ((h hb).subset hsub).mono (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
    (gridScale_ratio_rpow_le_of_cut_fine hδ (by exact_mod_cast hδ1) N hεpos hζ hgap hac hcb)))

/-- **The initial invariant of the stopping time.**  The whole grid `(0, N)` carries the block bound
as soon as the family satisfies the Katz–Tao hypothesis `Δ_max(𝕋) ≤ δ^{-ζ}` of GWZ Lemma 7.7(B): the
block `(0, N)` is the `δ`-nodes inside the top anchor `T_{i₀}^{(5)}`, so this is the leaf-to-node
transfer `isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre` at `σ_a = 1`, `σ_b = δ`.  The constant
depends on the ambient dimension and on `Cu`, never on `δ`. -/
theorem exists_blockKatzTao_zero_right (Cu : NNReal) (_hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E)
        (u : ∀ k, k ≤ N → Tube.IsUniformAtScale s T (gridScale δ N k) Cu)
        (ζ : ℝ), 0 ≤ ζ →
      maxDensity s (fibreBodies T δ) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) →
      BlockKatzTao u C ζ 0 N := by
  classical
  set n := Module.finrank ℝ E
  let cvol : NNReal := Tube.le_volume.c n
  let Bnn : NNReal := Tube.volume_le.C n * Cu ^ 3 * fibrePackConst n * (2 : NNReal) ^ n
  let C : NNReal := max 1 (Bnn / cvol)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro N hN ι δ hδ hδ1 hδ16 s T u ζ hζ hDensity i₀ hi₀ hbN
  let Y : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-ζ))
  let Δ : ENNReal := (C : ENNReal) * ENNReal.ofReal
    (((gridScale δ N 0 : ℝ) / (gridScale δ N N : ℝ)) ^ ζ)
  have hY_eq : ENNReal.ofReal (((gridScale δ N 0 : ℝ) / (gridScale δ N N : ℝ)) ^ ζ) = Y := by
    dsimp only [Y]
    rw [gridScale_zero, gridScale_self δ hN, NNReal.coe_one, one_div,
      ← Real.rpow_neg_eq_inv_rpow]
  have hΔ_def : Δ = (C : ENNReal) * Y := by
    dsimp only [Δ]; rw [hY_eq]
  have hKT : ∀ i₂ ∈ s, ConvexSpaceBody.IsKatzTao
      (fibreIndex s T (gridScale δ N N) (gridScale δ N 0) i₂)
      (fibreBodies T (gridScale δ N N)) Y := by
    have hDensity' : ConvexSpaceBody.IsKatzTao s (fibreBodies T (gridScale δ N N)) Y := by
      change maxDensity s (fibreBodies T (gridScale δ N N)) ≤ Y
      rw [gridScale_self δ hN]
      exact hDensity
    exact fun i₂ _ => hDensity'.subset (by simp [fibreIndex, Kakeya.familyIn])
  have hΔ : (Tube.volume_le.C n : ENNReal) * (Cu : ENNReal) ^ 2
        * (fibrePackConst n : ENNReal) * (2 : ENNReal) ^ n * Y
      ≤ Δ * (((u N hbN).branchingN : ENNReal) * (Tube.le_volume.c n : ENNReal)) := by
    rw [hΔ_def]
    let hb_nn : NNReal := (u N hbN).branchingN
    let A_nn : NNReal := Tube.volume_le.C n * Cu ^ 2 * fibrePackConst n * (2 : NNReal) ^ n
    have hcvol_pos : 0 < cvol := Tube.le_volume.c_pos n
    have h_one_le_nn : (1 : NNReal) ≤ Cu * hb_nn := one_le_mul_branchingN_atScale (u N hbN) hi₀
    have hBC : Bnn ≤ C * cvol :=
      (div_mul_cancel₀ Bnn hcvol_pos.ne').ge.trans (mul_le_mul' (le_max_right 1 _) le_rfl)
    have hA_nn_le : A_nn ≤ C * hb_nn * cvol := by
      calc
        A_nn = A_nn * 1 := by simp
        _ ≤ A_nn * (Cu * hb_nn) := mul_le_mul' le_rfl h_one_le_nn
        _ = Bnn * hb_nn := by dsimp [A_nn, Bnn]; ring
        _ ≤ (C * cvol) * hb_nn := mul_le_mul' hBC le_rfl
        _ = C * hb_nn * cvol := by ring
    have hA_cast : (Tube.volume_le.C n : ENNReal) * (Cu : ENNReal) ^ 2
          * (fibrePackConst n : ENNReal) * (2 : ENNReal) ^ n
        ≤ (C : ENNReal) * ((u N hbN).branchingN : ENNReal) * (Tube.le_volume.c n : ENNReal) := by
      simpa [A_nn, hb_nn] using ENNReal.coe_le_coe.mpr hA_nn_le
    exact (mul_le_mul' hA_cast le_rfl).trans_eq (by ring)
  exact isKatzTao_gapNodeIndex_of_isKatzTao_gapFibre_atScale
    (ub := u N hbN) (σa := gridScale δ N 0) (σb := gridScale δ N N) (Y := Y) (Δ := Δ)
    (gridScale_pos hδ N 0) (gridScale_self δ hN).ge ((gridScale_self δ hN).trans_le hδ1)
    (by rw [gridScale_self δ hN, gridScale_zero]; exact hδ16) hΔ hKT hi₀

end Blocks

end MultiScaleFac

end Kakeya
