/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.ChainFibre
public import Kakeya.MultiScaleFac.Product

/-!
# The product lemma of GWZ Lemma 7.7(A), final form

`maxDensity_fibre_le_prod_mul_branchingN` leaves the maximal density of the fibre bounded by the
product of the per-gap Frostman bounds times `N_{σ₁} (δ/σ₁)^{n-1}`.  Dividing by the anchor
density turns that into the Frostman constant of the fibre, and
`branchingN_mul_le_densityIn` is exactly the identification that makes the division exact up to a
dimensional constant.  Nothing here depends on `δ`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The chain half of the product lemma, with the constant ahead of the block index.**  This is
`Kakeya.MultiScaleFac.maxDensity_fibre_le_prod_mul_branchingN` with `J` quantified after the
constant: one constant serves every block index, which is what the grid-length-dependent chain
of GWZ Lemma 7.7(A) needs.  Nothing else differs. -/
private theorem maxDensity_fibre_le_prod_mul_branchingN_uniform (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (J : ℕ) {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (σ : ℕ → NNReal), σ 0 = 1 → σ (J + 2) = δ → Antitone σ →
      (∀ m : Fin (J + 2), 16 * σ (m.succ : ℕ) ≤ σ (m.castSucc : ℕ)) →
      ∀ (𝒰 : ChainUniformTubeSet s T (J + 2) σ Cu),
      ∀ (X : Fin (J + 2) → ENNReal), (∀ m, X m ≠ ⊤) →
      (∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
        ConvexSpaceBody.IsFrostmanIn
          (fibreIndex s T δ (σ (m.castSucc : ℕ)) i₁) (fibreBodies T (σ (m.succ : ℕ)))
          ((T i₁).rescale (2 * σ (m.castSucc : ℕ))).toConvexSpaceBody (X m)) →
      ∀ i₀ ∈ s,
      maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody)
        ≤ (C : ENNReal) ^ (J + 2) * (∏ m : Fin (J + 1), X m.succ)
            * ((𝒰.branchingN 1
                * (δ ^ (Module.finrank ℝ E - 1) / σ 1 ^ (Module.finrank ℝ E - 1))
                : NNReal) : ENNReal) := by
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set Cw : NNReal := Cu ^ 2 with hCw
  set G := gapProdConst n Cw with hG
  obtain ⟨Ce, hCe_pos, hengine⟩ :=
    maxDensity_fibre_le_prod_of_grid_cuts_nodes_uniform (E := E) Cu hCu
  set C := ((1 : NNReal) ⊔ Ce.toNNReal) * ((1 : NNReal) ⊔ Cw) * ((1 : NNReal) ⊔ G) with hC_def
  have hsCe : (1 : NNReal) ≤ 1 ⊔ Ce.toNNReal := le_max_left _ _
  have hsCw : (1 : NNReal) ≤ 1 ⊔ Cw := le_max_left _ _
  have hsG : (1 : NNReal) ≤ 1 ⊔ G := le_max_left _ _
  have hC_one : 1 ≤ C := by
    simpa using mul_le_mul' (mul_le_mul' hsCe hsCw) hsG
  refine ⟨C, hC_one, ?_⟩
  intro J ι δ hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 X hXtop hFr i₀ hi₀
  have hδσ : ∀ k ≤ J + 2, δ ≤ σ k := fun k hk => by rw [← hσlast]; exact hanti hk
  have hσne : ∀ k ≤ J + 2, σ k ≠ 0 := fun k hk => (hδ.trans_le (hδσ k hk)).ne'
  have hσ1 : ∀ k, σ k ≤ 1 := fun k => by rw [← hσ0]; exact hanti (Nat.zero_le k)
  have hN : ∀ k ≤ J + 2, 𝒰.branchingN k ≠ 0 := fun k hk hzero => by
    simpa [hzero] using one_le_mul_branchingN 𝒰 hCu hk hi₀
  set Δ : Fin (J + 2) → ENNReal := fun m =>
    if m = 0 then (Cw : ENNReal) else
      X m * ((G * (𝒰.branchingN (m.castSucc : ℕ) / 𝒰.branchingN (m.succ : ℕ))
        * (σ (m.succ : ℕ) ^ p / σ (m.castSucc : ℕ) ^ p) : NNReal) : ENNReal) with hΔ_def
  have hΔtop : ∀ m, Δ m ≠ ⊤ := by
    intro m
    dsimp only [Δ]
    split_ifs
    · exact ENNReal.coe_ne_top
    · exact ENNReal.mul_ne_top (hXtop m) ENNReal.coe_ne_top
  have hΔ0 : (Cw : ENNReal) ≤ Δ 0 := by
    simp [Δ]
  have hΔKT : ∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
      ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 (m.succ : ℕ) i₁ (5 * σ (m.castSucc : ℕ)))
        (fun j => (𝒰.cover.tube (m.succ : ℕ) j).toConvexSpaceBody) (Δ m) := by
    intro m hm i₁ hi₁
    simp only [Δ, if_neg hm]
    have hm' := m.isLt
    have hkc : ((m.castSucc : Fin (J + 3)) : ℕ) ≤ J + 2 := by
      simp only [Fin.val_castSucc]; omega
    have hks : ((m.succ : Fin (J + 3)) : ℕ) ≤ J + 2 := by
      simp only [Fin.val_succ]; omega
    exact isKatzTao_gapNode_of_isFrostmanIn 𝒰 hCu hkc hks (hδ.trans_le (hδσ _ hkc))
      (hδσ _ hks) (hσ1 _)
      ((mul_le_mul_left (by norm_num : (2 : NNReal) ≤ 16) _).trans (hgap m))
      (hN _ hks) (hFr m hm) hi₁
  have hmax := hengine J hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 Δ hΔtop hΔ0 hΔKT i₀ hi₀
  have hprod_eq : (∏ m : Fin (J + 2), Δ m) = (Cw : ENNReal) * (∏ m : Fin (J + 1), X m.succ)
      * ((G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2))
          * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal) := by
    have h := prod_gapDelta_eq σ 𝒰 hN hσne X
    rwa [hσlast] at h
  rw [hprod_eq] at hmax
  have hN_last_ne_zero : 𝒰.branchingN (J + 2) ≠ 0 := hN (J + 2) le_rfl
  have hCpow : Ce.toNNReal ^ (J + 2) * Cw ^ 2 * G ^ (J + 1) ≤ C ^ (J + 2) := by
    rw [hC_def, mul_pow, mul_pow]
    calc
      Ce.toNNReal ^ (J + 2) * Cw ^ 2 * G ^ (J + 1)
          ≤ ((1 : NNReal) ⊔ Ce.toNNReal) ^ (J + 2) * ((1 : NNReal) ⊔ Cw) ^ 2
              * ((1 : NNReal) ⊔ G) ^ (J + 1) := by gcongr <;> exact le_max_right _ _
      _ ≤ ((1 : NNReal) ⊔ Ce.toNNReal) ^ (J + 2) * ((1 : NNReal) ⊔ Cw) ^ (J + 2)
            * ((1 : NNReal) ⊔ G) ^ (J + 2) := by gcongr <;> omega
  have h_simplify : ENNReal.ofReal Ce ^ (J + 2)
      * ((Cw : ENNReal) * (𝒰.branchingN (J + 2) : ENNReal))
      * ((Cw : ENNReal) * (∏ m : Fin (J + 1), X m.succ)
        * ((G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2))
            * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal))
      ≤ (C : ENNReal) ^ (J + 2) * (∏ m : Fin (J + 1), X m.succ)
          * ((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal) := by
    have hkey : Ce.toNNReal ^ (J + 2) * Cw ^ 2
          * (G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2)) * (δ ^ p / σ 1 ^ p))
          * 𝒰.branchingN (J + 2)
        ≤ C ^ (J + 2) * (𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p)) := by
      calc
        Ce.toNNReal ^ (J + 2) * Cw ^ 2
            * (G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2)) * (δ ^ p / σ 1 ^ p))
            * 𝒰.branchingN (J + 2)
            = (Ce.toNNReal ^ (J + 2) * Cw ^ 2 * G ^ (J + 1))
              * ((𝒰.branchingN 1 / 𝒰.branchingN (J + 2) * 𝒰.branchingN (J + 2))
                * (δ ^ p / σ 1 ^ p)) := by ring
        _ = (Ce.toNNReal ^ (J + 2) * Cw ^ 2 * G ^ (J + 1))
              * (𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p)) := by
          rw [div_mul_cancel₀ _ hN_last_ne_zero]
        _ ≤ C ^ (J + 2) * (𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p)) := mul_le_mul_left hCpow _
    have hL : ENNReal.ofReal Ce ^ (J + 2)
        * ((Cw : ENNReal) * (𝒰.branchingN (J + 2) : ENNReal))
        * ((Cw : ENNReal) * (∏ m : Fin (J + 1), X m.succ)
          * ((G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2))
              * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal))
        = ((Ce.toNNReal ^ (J + 2) * Cw ^ 2
            * (G ^ (J + 1) * (𝒰.branchingN 1 / 𝒰.branchingN (J + 2)) * (δ ^ p / σ 1 ^ p))
            * 𝒰.branchingN (J + 2) : NNReal) : ENNReal) * (∏ m : Fin (J + 1), X m.succ) := by
      rw [show ENNReal.ofReal Ce = (Ce.toNNReal : ENNReal) from rfl]
      push_cast
      ring
    have hR : (C : ENNReal) ^ (J + 2) * (∏ m : Fin (J + 1), X m.succ)
        * ((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal)
        = ((C ^ (J + 2) * (𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p)) : NNReal) : ENNReal)
          * (∏ m : Fin (J + 1), X m.succ) := by
      push_cast
      ring
    rw [hL, hR]
    exact mul_le_mul_left (ENNReal.coe_le_coe.mpr hkey) _
  exact hmax.trans h_simplify

/-- **The maximal density of the fibre against the anchor density.**  The last surviving branching
number is traded for the density of the family in the anchor body, which is exactly the denominator
in `frostmanConstant_eq_maxDensity_div`.  The constant is quantified before the block index `J`, so
one constant serves every block length. -/
private theorem maxDensity_fibre_le_prod_mul_densityIn (Cu Cf : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (J : ℕ) {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (σ : ℕ → NNReal), σ 0 = 1 → σ (J + 2) = δ → Antitone σ →
      (∀ m : Fin (J + 2), 16 * σ (m.succ : ℕ) ≤ σ (m.castSucc : ℕ)) →
      ∀ (_𝒰 : ChainUniformTubeSet s T (J + 2) σ Cu),
      (∀ i₁ ∈ s, ∀ i₂ ∈ s,
        ((fibreIndex s T δ (σ 1) i₁).card : NNReal)
          ≤ Cf * ((fibreIndex s T δ (σ 1) i₂).card : NNReal)) →
      ∀ (X : Fin (J + 2) → ENNReal), (∀ m, X m ≠ ⊤) →
      (∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
        ConvexSpaceBody.IsFrostmanIn
          (fibreIndex s T δ (σ (m.castSucc : ℕ)) i₁) (fibreBodies T (σ (m.succ : ℕ)))
          ((T i₁).rescale (2 * σ (m.castSucc : ℕ))).toConvexSpaceBody (X m)) →
      ∀ i₀ ∈ s,
      maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody)
        ≤ (C : ENNReal) ^ (J + 2) * (∏ m : Fin (J + 1), X m.succ)
            * Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
                ((T i₀).rescale (σ 1)).toConvexSpaceBody := by
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set c := Tube.le_volume.c n with hc
  set Cv := Tube.volume_le.C n with hCv
  set PK := fibrePackConst n with hPK
  set K := PK * Cu ^ 2 * Cf * (6 * Cv) with hK
  have hc_pos : 0 < (c : ℝ) := Tube.le_volume.c_pos n
  have hc_ne : c ≠ 0 := by exact_mod_cast hc_pos.ne'
  obtain ⟨C₁, hC₁, hchain⟩ := maxDensity_fibre_le_prod_mul_branchingN_uniform (E := E) Cu hCu
  set C := C₁ * ((1 : NNReal) ⊔ (K / c)) with hC_def
  have hsK : (1 : NNReal) ≤ 1 ⊔ (K / c) := le_max_left _ _
  have hC_one : 1 ≤ C := by
    simpa using mul_le_mul' hC₁ hsK
  refine ⟨C, hC_one, ?_⟩
  intro J ι δ hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 hcmp X hXtop hFr i₀ hi₀
  have hδσ : ∀ k ≤ J + 2, δ ≤ σ k := fun k hk => by rw [← hσlast]; exact hanti hk
  have hσ1le : σ 1 ≤ 1 := by rw [← hσ0]; exact hanti (Nat.zero_le 1)
  have hσ1pos : 0 < σ 1 := hδ.trans_le (hδσ 1 (by omega))
  have h2δ : 2 * δ ≤ σ 1 := by
    have hg := hgap (1 : Fin (J + 2))
    rw [show ((1 : Fin (J + 2)).castSucc : ℕ) = 1 from by simp,
      show ((1 : Fin (J + 2)).succ : ℕ) = 2 from by simp] at hg
    exact (mul_le_mul' (by norm_num : (2 : NNReal) ≤ 16) (hδσ 2 (by omega))).trans hg
  have hN_nonzero : 𝒰.branchingN 1 ≠ 0 := fun hzero => by
    simpa [hzero] using one_le_mul_branchingN 𝒰 hCu (by omega : (1 : ℕ) ≤ J + 2) hi₀
  have hmax := hchain J hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 X hXtop hFr i₀ hi₀
  set P := ∏ m : Fin (J + 1), X m.succ with hP
  set D := Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
    ((T i₀).rescale (σ 1)).toConvexSpaceBody with hD
  have hden : (𝒰.branchingN 1 : ENNReal) * ((c : ENNReal) * ((δ : ENNReal) ^ p))
      ≤ ((K : NNReal) : ENNReal) * (((σ 1 : ENNReal) ^ p) * D) := by
    have hden_raw := branchingN_mul_le_densityIn 𝒰 hCu (by omega : (1 : ℕ) ≤ J + 2)
      hσ1pos h2δ hσ1le hcmp hi₀
    simpa [K, PK, Cv, hc, p, hn] using hden_raw
  set A : ENNReal := (c : ENNReal) * ((σ 1 : ENNReal) ^ p) with hA
  have hA_nonzero : A ≠ 0 := by
    rw [hA]
    exact mul_ne_zero (by exact_mod_cast hc_pos.ne')
      (pow_ne_zero p (by exact_mod_cast hσ1pos.ne'))
  have hA_finite : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hprod_simp : ((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal) * A
      = (𝒰.branchingN 1 : ENNReal) * ((c : ENNReal) * ((δ : ENNReal) ^ p)) := by
    have hnn : (𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) * (c * σ 1 ^ p)
        = 𝒰.branchingN 1 * (c * δ ^ p) := by
      apply NNReal.eq
      have hσ1R : (σ 1 : ℝ) ≠ 0 := by exact_mod_cast hσ1pos.ne'
      field_simp
    calc ((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal) * A
        = (((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) * (c * σ 1 ^ p) : NNReal) : ENNReal) := by
          rw [hA]; push_cast; ring
      _ = ((𝒰.branchingN 1 * (c * δ ^ p) : NNReal) : ENNReal) := by rw [hnn]
      _ = (𝒰.branchingN 1 : ENNReal) * ((c : ENNReal) * ((δ : ENNReal) ^ p)) := by push_cast; ring
  have hK_bound : ((K : NNReal) : ENNReal)
      ≤ (((1 : NNReal) ⊔ (K / c : NNReal)) : ENNReal) ^ (J + 2) * (c : ENNReal) := by
    have hKnn : K ≤ ((1 : NNReal) ⊔ (K / c)) ^ (J + 2) * c := by
      calc K = K / c * c := by field_simp
        _ ≤ ((1 : NNReal) ⊔ (K / c)) ^ (J + 2) * c := by
          gcongr
          exact (le_max_right _ _).trans
            (by simpa using pow_le_pow_right₀ hsK (by omega : 1 ≤ J + 2))
    exact_mod_cast hKnn
  have hgoalA : maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody) * A
      ≤ ((C : ENNReal) ^ (J + 2) * P * D) * A := by
    calc
      maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody) * A
          ≤ ((C₁ : ENNReal) ^ (J + 2) * P
              * ((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal)) * A :=
        mul_le_mul_left hmax A
      _ = (C₁ : ENNReal) ^ (J + 2) * P
            * (((𝒰.branchingN 1 * (δ ^ p / σ 1 ^ p) : NNReal) : ENNReal) * A) := by ring
      _ = (C₁ : ENNReal) ^ (J + 2) * P
            * ((𝒰.branchingN 1 : ENNReal) * ((c : ENNReal) * ((δ : ENNReal) ^ p))) := by
        rw [hprod_simp]
      _ ≤ (C₁ : ENNReal) ^ (J + 2) * P
            * ((((1 : NNReal) ⊔ (K / c : NNReal)) : ENNReal) ^ (J + 2) * (c : ENNReal)
              * (((σ 1 : ENNReal) ^ p) * D)) :=
        mul_le_mul_right (hden.trans (mul_le_mul_left hK_bound _)) _
      _ = ((C : ENNReal) ^ (J + 2) * P * D) * A := by
        rw [hA, hC_def]
        push_cast
        ring
  exact (ENNReal.mul_le_mul_iff_left hA_nonzero hA_finite).mp hgoalA

/-- **The product lemma of GWZ Lemma 7.7(A): Frostman constants multiply along a chain.**  For a
chain `1 = σ₀ ≥ … ≥ σ_{J+2} = δ` of `16`-separated scales at each of which `𝕋` is `Cu`-uniform and
whose exact-scale fibre counts at `σ₁` are `Cf`-comparable, per-gap Frostman bounds `X_m` at the
gaps `m ≠ 0` give `C_F(𝕋[i₀; σ₁], T_{i₀}^{(σ₁)}) ≤ C ^ (J+2) · ∏ m, X m`, with `C` depending only
on the ambient dimension, on `Cu` and on `Cf` — never on `J` and never on `δ`. -/
theorem frostmanConstant_fibre_le_prod (Cu Cf : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (J : ℕ) {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (σ : Fin (J + 3) → NNReal), σ 0 = 1 → σ (Fin.last (J + 2)) = δ → Antitone σ →
      (∀ m : Fin (J + 2), 16 * σ m.succ ≤ σ m.castSucc) →
      ∀ (_𝒰 : ChainUniformTubeSet s T (J + 2) (finChain σ) Cu),
      (∀ i₁ ∈ s, ∀ i₂ ∈ s,
        ((fibreIndex s T δ (σ 1) i₁).card : NNReal)
          ≤ Cf * ((fibreIndex s T δ (σ 1) i₂).card : NNReal)) →
      ∀ (X : Fin (J + 2) → ENNReal), (∀ m, X m ≠ ⊤) → 1 ≤ X 0 →
      (∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
        ConvexSpaceBody.IsFrostmanIn
          (fibreIndex s T δ (σ m.castSucc) i₁) (fibreBodies T (σ m.succ))
          ((T i₁).rescale (2 * σ m.castSucc)).toConvexSpaceBody (X m)) →
      ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (σ 1) i₀) (fibreBodies T δ)
            ((T i₀).rescale (σ 1)).toConvexSpaceBody
          ≤ (C : ENNReal) ^ (J + 2) * ∏ m, X m := by
  obtain ⟨C, hC, hmain⟩ :=
    maxDensity_fibre_le_prod_mul_densityIn (E := E) Cu Cf hCu
  refine ⟨C, hC, ?_⟩
  intro J ι δ hδ hδ1 s T hball σ hσ0 hσlast hanti hgap 𝒰 hcmp X hXtop hX0 hFr i₀ hi₀
  have hcmp' : ∀ i₁ ∈ s, ∀ i₂ ∈ s,
      ((fibreIndex s T δ (finChain σ 1) i₁).card : NNReal)
        ≤ Cf * ((fibreIndex s T δ (finChain σ 1) i₂).card : NNReal) := by
    rw [finChain_one]
    exact hcmp
  have hgap' : ∀ m : Fin (J + 2),
      16 * finChain σ (m.succ : ℕ) ≤ finChain σ (m.castSucc : ℕ) := by
    intro m
    rw [finChain_coe σ m.succ, finChain_coe σ m.castSucc]
    exact hgap m
  have hFr' : ∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
      ConvexSpaceBody.IsFrostmanIn
        (fibreIndex s T δ (finChain σ (m.castSucc : ℕ)) i₁)
        (fibreBodies T (finChain σ (m.succ : ℕ)))
        ((T i₁).rescale (2 * finChain σ (m.castSucc : ℕ))).toConvexSpaceBody (X m) := by
    intro m hm i₁ hi₁
    rw [finChain_coe σ m.castSucc, finChain_coe σ m.succ]
    exact hFr m hm i₁ hi₁
  have hmax := hmain J hδ hδ1 s T hball (finChain σ)
    (by rw [finChain_zero]; exact hσ0) (by rw [finChain_last]; exact hσlast)
    (finChain_antitone hanti) hgap' 𝒰 hcmp' X hXtop hFr' i₀ hi₀
  rw [finChain_one] at hmax
  have hPle : (∏ m : Fin (J + 1), X m.succ) ≤ ∏ m : Fin (J + 2), X m := by
    rw [Fin.prod_univ_succ (f := X)]
    simpa using mul_le_mul_left hX0 (∏ m : Fin (J + 1), X m.succ)
  have hDensity : Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
        ((T i₀).rescale (σ 1)).toConvexSpaceBody
      = Kakeya.densityIn (fibreIndex s T δ (σ 1) i₀) (fibreBodies T δ)
        ((T i₀).rescale (σ 1)).toConvexSpaceBody := by
    rw [Kakeya.densityIn_eq_densityIn_filter]
    simp [fibreIndex, Kakeya.familyIn]
  have hmaxDensity : maxDensity (fibreIndex s T δ (σ 1) i₀) (fibreBodies T δ)
      ≤ ((C : ENNReal) ^ (J + 2) * ∏ m, X m)
        * Kakeya.densityIn (fibreIndex s T δ (σ 1) i₀) (fibreBodies T δ)
        ((T i₀).rescale (σ 1)).toConvexSpaceBody := by
    rw [← hDensity]
    calc
      maxDensity (fibreIndex s T δ (σ 1) i₀) (fibreBodies T δ)
          = maxDensity (fibreIndex s T δ (σ 1) i₀) (fun i => (T i).toConvexSpaceBody) := by
        simp
      _ ≤ (C : ENNReal) ^ (J + 2) * (∏ m : Fin (J + 1), X m.succ)
          * Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
              ((T i₀).rescale (σ 1)).toConvexSpaceBody := hmax
      _ ≤ ((C : ENNReal) ^ (J + 2) * ∏ m, X m)
          * Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
              ((T i₀).rescale (σ 1)).toConvexSpaceBody :=
        mul_le_mul_left (mul_le_mul_right hPle _) _
  exact ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
    (ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le hmaxDensity)

end MultiScaleFac

end Kakeya
