/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.BoxLocalization

/-!
# Tube-scale density of the shared-slab thickened shading (Item 2 of GWZ Lemma 6.13)

Item 2 of `Kakeya.plankReduction` asks, for each used slab `S`, for a density
`c₂ · a^{4η} ≤ λ(𝒯_S, Yθ)` of the thickened shading, where
`Yθ Q` is the shared-slab thickened shading of `Q` (undilated, for exposition) and has

* `carrier = Q.carrier`, and
* `shade   = Q.carrier ∩ U_S`, where `U_S = ⋃_{i ∈ P^ass_S} (Y' i).shade` is the shading union
  of the **whole** assigned plank family of the slab, not of `Q`'s own `repr`-fibre.

So Item 2 is a genuine *dense-box* statement about how `U_S` fills the representative prisms; it is
not implied by (nor does it imply) any bound relating the common fibre size `N` to `θ b / a`.

This file contains the box-level ingredients that statement is consumed through: the box-to-prism
density transfer, the cross-frame containment of a grid box in a dilated representative, and the
incidence and Markov bookkeeping of the deletion layer.  All constants are quantified before every
geometric datum; nothing here assumes a lower bound on `N`, a bound on `N_ov / N`, or any relation
between `a`, `b` and `θ` beyond what is written in each statement.

## Main results

* `Plank.density_transfer_of_boxes` — the **grid bridge**: boxes `B q ⊆ Q` that are individually
  `t`-dense for `U`, cover a `κ`-fraction of `Q`, and overlap at most `m`-fold, force
  `t · κ · |Q| ≤ m · |U ∩ Q|`.  This is the shape in which `Plank.denseBoxEstimate_weighted`
  (a `θb × b × b` box statement) would be summed along a `θb × b × 1` representative, with
  `Plank.shiftedSlabBox_sum_inter_volume_le` supplying `m = 8`.
* `Plank.shiftedSlabBox_subset_dilation_of_meet_dilation` — a grid box meeting a fixed dilation of
  a representative sits in a larger fixed dilation of it.  The boxes are aligned with `S`, the
  prism with its own frame, and the two differ by the controlled angle `Cang · θ`; this is what
  makes the fixed dilation necessary.
* `Plank.card_tangentialBoxes_mul_le`, `Plank.sum_card_tangential_mul_le` — one plank is tangential
  to at most `64 c_tan / b` boxes of a fixed shift, in the summed form the deletion layer needs.
* `Plank.markov_mass_split` — the generic Markov/deletion step over a finite family of boxes.

The remaining gaps along this route are the hypothesis `(★)` itself (equivalently, a
per-representative tube-scale density), and inside that: the local input (5); the passage from a
mass-level good-box set to a good-box cover of each individual representative; and the
bounded-overlap bound for *dilated* representatives.  See the blueprint node `lem:tubeScaleDensity`
for the exact missing inequalities.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## The grid bridge: from box density to prism density -/

/-- **Box-to-prism density transfer** (`lem:densityTransferOfBoxes`).  If finitely many sets
`B q ⊆ Q` are individually `t`-dense for `U` (`t · |B q| ≤ |U ∩ B q|`), together cover a
`κ`-fraction of `Q` (`κ · |Q| ≤ ∑_q |B q|`), and overlap at most `m`-fold on `U ∩ Q` in the sense
that `∑_q |(U ∩ Q) ∩ B q| ≤ m · |U ∩ Q|`, then

`t · κ · |Q| ≤ m · |U ∩ Q|`.

This is the only step that converts the `θb × b × b` scale of `Plank.denseBoxEstimate_weighted`
into the `θb × b × 1` scale of a representative prism: a representative is covered by `≍ b⁻¹`
grid boxes, so `κ` is an absolute constant, and for the boxes of a *single fixed shift*
`Plank.shiftedSlabBox_sum_inter_volume_le` supplies the overlap hypothesis with the absolute
`m = 8`.  Everything is stated for arbitrary sets: no measurability, convexity or disjointness is
needed, only the three displayed inequalities. -/
theorem density_transfer_of_boxes {β : Type*} (D : Finset β)
    (B : β → Set (EuclideanSpace ℝ (Fin 3))) (Q U : Set (EuclideanSpace ℝ (Fin 3)))
    (t κ m : ENNReal)
    (hsub : ∀ q ∈ D, B q ⊆ Q)
    (hdense : ∀ q ∈ D, t * volume (B q) ≤ volume (U ∩ B q))
    (hcover : κ * volume Q ≤ ∑ q ∈ D, volume (B q))
    (hoverlap : ∑ q ∈ D, volume ((U ∩ Q) ∩ B q) ≤ m * volume (U ∩ Q)) :
    t * κ * volume Q ≤ m * volume (U ∩ Q) := by
  calc
    t * κ * volume Q = t * (κ * volume Q) := mul_assoc ..
    _ ≤ t * ∑ q ∈ D, volume (B q) := mul_le_mul_right hcover t
    _ = ∑ q ∈ D, t * volume (B q) := Finset.mul_sum ..
    _ ≤ ∑ q ∈ D, volume ((U ∩ Q) ∩ B q) := Finset.sum_le_sum fun q hq => by
        rw [Set.inter_assoc, Set.inter_eq_right.mpr (hsub q hq)]; exact hdense q hq
    _ ≤ m * volume (U ∩ Q) := hoverlap

/-! ## The covering fraction: grid boxes inside a dilated representative -/

/-- **Cross-frame diameter of a grid box.**  Two points of the same shifted grid box
`shiftedSlabBox S b t q` differ, in the direction of any vector `v`, by at most the `S`-frame
spread `2θb·|⟪v,e₀⟫| + 2b·|⟪v,e₁⟫| + 2b·|⟪v,e₂⟫|`.  No relation between the frames is used; this is
the box's own coordinate description followed by `Plank.abs_inner_le_sum_frame_bound`. -/
theorem abs_inner_sub_le_of_mem_shiftedSlabBox {θ b : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (t : Fin 3 → ℝ) (q : Fin 3 → ℤ) {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hy : y ∈ ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (v : EuclideanSpace ℝ (Fin 3)) :
    |(inner ℝ v (y - x) : ℝ)|
      ≤ 2 * ((θ : ℝ) * (b : ℝ)) * |(inner ℝ v (S.basis 0) : ℝ)|
        + 2 * (b : ℝ) * |(inner ℝ v (S.basis 1) : ℝ)|
        + 2 * (b : ℝ) * |(inner ℝ v (S.basis 2) : ℝ)| := by
  have key : ∀ j : Fin 3, |S.basis.repr (y - x) j| ≤ 2 * ((![θ * b, b, b] j : ℝ≥0) : ℝ) := by
    intro j
    have hxj := (mem_shiftedSlabBox_iff S b t q x).mp hx j
    have hyj := (mem_shiftedSlabBox_iff S b t q y).mp hy j
    have hsub : S.basis.repr (y - x) j
        = S.basis.repr (y -ᵥ S.center) j - S.basis.repr (x -ᵥ S.center) j := by
      rw [show (y - x : EuclideanSpace ℝ (Fin 3)) = (y -ᵥ S.center) - (x -ᵥ S.center) from
        (sub_sub_sub_cancel_right y x S.center).symm, S.basis.repr.map_sub]
      rfl
    rw [hsub, two_mul]
    exact (abs_sub_le _ _ _).trans (add_le_add hyj (by rwa [abs_sub_comm]))
  have h := abs_inner_le_sum_frame_bound S.basis v (y - x) _ key
  rw [Fin.sum_univ_three] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, NNReal.coe_mul] at h
  exact h

/-- **The shared computation behind both box-meets-representative containments.**

A grid box `B_q` aligned with the slab `S` that meets the `Cc`-dilation of a `θb × b × 1`
representative `P` whose plane angle with `S` is at most `Cang · θ` is contained in the
`(4·Cang + 7 + Cc)`-dilation of `P`.  Let `y0 ∈ B_q ∩ P^{(Cc)}` and `y ∈ B_q`.  In the thin
direction of `P` the spread of the box is at most `2θb + 4b·Cang·θ` and
`|⟨u₀, y0 - P.center⟩| ≤ Cc·θb`, giving `θb(2 + 4Cang + Cc)`; in the middle direction `6b + Cc·b`;
along the long axis `6b + Cc ≤ 6 + Cc`.  Each is at most `4Cang + 7 + Cc` times the corresponding
half-width.

The constant is stated as `4·Cang + 7 + Cc` rather than the `4·Cang + 8 + Cc` the callers use
because that is what the computation actually gives, and because `Cc = 1` then reproduces the
undilated constant `4·Cang + 8` on the nose. -/
private theorem shiftedSlabBox_subset_dilation_core
    {θ b : ℝ≥0} {hθb : θ * b ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (S : Slab θ hθ1) (t : Fin 3 → ℝ) (q : Fin 3 → ℤ)
    (P : Prism3D (θ * b) b 1 hθb hb1) (Cang Cc : ℝ≥0) (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc)
    (hθ0 : 0 < θ) (hb0 : 0 < b)
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ))
    (hmeet : (((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      ((P.toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty) :
    ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.toPrismNDim.dilation (4 * Cang + 7 + Cc)).carrier := by
  -- Pick a point `y0` in the intersection `B_q ∩ P^{(Cc)}`.
  obtain ⟨y0, hy0_box, hy0_P⟩ := hmeet
  intro y hy
  have hbox_inner (v : EuclideanSpace ℝ (Fin 3)) :
      |(inner ℝ v (y - y0) : ℝ)|
        ≤ 2 * ((θ : ℝ) * (b : ℝ)) * |(inner ℝ v (S.basis 0) : ℝ)|
          + 2 * (b : ℝ) * |(inner ℝ v (S.basis 1) : ℝ)|
          + 2 * (b : ℝ) * |(inner ℝ v (S.basis 2) : ℝ)| :=
    abs_inner_sub_le_of_mem_shiftedSlabBox S t q hy0_box hy _
  have hθ_nonneg : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg _
  have hb_nonneg : 0 ≤ (b : ℝ) := NNReal.coe_nonneg _
  have hθ_pos : 0 < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hb_pos : 0 < (b : ℝ) := NNReal.coe_pos.mpr hb0
  have hθ_le_one : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hb_le_one : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hCang_ge_one : (1 : ℝ) ≤ (Cang : ℝ) := by exact_mod_cast hCang
  have hCc_ge_one : (1 : ℝ) ≤ (Cc : ℝ) := by exact_mod_cast hCc
  have hθb_nonneg : (0 : ℝ) ≤ (θ : ℝ) * (b : ℝ) := mul_nonneg hθ_nonneg hb_nonneg
  have hb_one_sub : (0 : ℝ) ≤ (b : ℝ) * (1 - (θ : ℝ)) :=
    mul_nonneg hb_nonneg (sub_nonneg.mpr hθ_le_one)
  have hb_Cang_sub : (0 : ℝ) ≤ (b : ℝ) * ((Cang : ℝ) - 1) :=
    mul_nonneg hb_nonneg (sub_nonneg.mpr hCang_ge_one)
  -- Angle bound: for `j ≠ 0`, `|⟨P.basis 0, S.basis j⟩| ≤ Cang * θ`.
  have h_angle_bound (j : Fin 3) (hj : j ≠ 0) :
      |inner ℝ (P.basis 0) (S.basis j)| ≤ (Cang : ℝ) * (θ : ℝ) := by
    rw [real_inner_comm]
    exact (abs_inner_basis_ne_zero_le_angle S P hj).trans (Prism3D.angle_comm P S ▸ hang)
  -- Cauchy-Schwarz bound: `|⟨P.basis i, S.basis j⟩| ≤ 1`, both being unit vectors.
  have h_cs_bound (i j : Fin 3) : |inner ℝ (P.basis i) (S.basis j)| ≤ 1 := by
    have h := abs_real_inner_le_norm (P.basis i) (S.basis j)
    rwa [P.basis.norm_eq_one i, S.basis.norm_eq_one j, mul_one] at h
  have hP_thickness : P.thicknesses = ![θ * b, b, 1] := Prism3D.thicknesses_eq P
  -- `y0 ∈ (P.dilation Cc).carrier` bounds its coordinates in the frame of `P`.
  have hy0_P_coord (i : Fin 3) :
      |P.basis.repr (y0 -ᵥ P.center) i| ≤ (Cc : ℝ) * ((P.thicknesses i : ℝ≥0) : ℝ) := by
    have h := ((P.toPrismNDim.dilation Cc).mem_carrier_iff y0).mp hy0_P i
    simpa only [PrismNDim.dilation_center, PrismNDim.dilation_basis,
      PrismNDim.dilation_thicknesses, NNReal.coe_mul] using h
  have h_repr_decomp (i : Fin 3) : P.basis.repr (y -ᵥ P.center) i
      = inner ℝ (P.basis i) (y - y0) + P.basis.repr (y0 -ᵥ P.center) i := by
    rw [P.basis.repr_apply_apply, P.basis.repr_apply_apply, ← inner_add_right]
    simp only [vsub_eq_sub, sub_add_sub_cancel]
  have ht0 : P.thicknesses 0 = θ * b := by rw [hP_thickness]; rfl
  have ht1 : P.thicknesses 1 = b := by rw [hP_thickness]; rfl
  have ht2 : P.thicknesses 2 = 1 := by rw [hP_thickness]; rfl
  have h2b : (0 : ℝ) ≤ 2 * (b : ℝ) := mul_nonneg zero_le_two hb_nonneg
  have h2θb : (0 : ℝ) ≤ 2 * ((θ : ℝ) * (b : ℝ)) := mul_nonneg zero_le_two hθb_nonneg
  -- The box spreads in the direction of `v` by `2θb·α + 2b·β + 2b·γ` whenever `α, β, γ` bound the
  -- three frame entries of `v`.
  have hspread (v : EuclideanSpace ℝ (Fin 3)) {α β γ : ℝ}
      (h0 : |(inner ℝ v (S.basis 0) : ℝ)| ≤ α) (h1 : |(inner ℝ v (S.basis 1) : ℝ)| ≤ β)
      (h2 : |(inner ℝ v (S.basis 2) : ℝ)| ≤ γ) :
      |(inner ℝ v (y - y0) : ℝ)|
        ≤ 2 * ((θ : ℝ) * (b : ℝ)) * α + 2 * (b : ℝ) * β + 2 * (b : ℝ) * γ :=
    (hbox_inner v).trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 h2θb)
      (mul_le_mul_of_nonneg_left h1 h2b)) (mul_le_mul_of_nonneg_left h2 h2b))
  -- In the thin direction of `P` the box spreads by at most `2θb + 4b·Cang·θ`, because the two
  -- off-diagonal frame entries of `P.basis 0` are controlled by the angle.
  have hthin : |inner ℝ (P.basis 0) (y - y0)|
      ≤ 2 * ((θ : ℝ) * (b : ℝ)) + 4 * (b : ℝ) * ((Cang : ℝ) * (θ : ℝ)) :=
    (hspread (P.basis 0) (h_cs_bound 0 0) (h_angle_bound 1 (by decide))
      (h_angle_bound 2 (by decide))).trans (le_of_eq (by ring))
  -- In every direction it spreads by at most `2θb + 4b ≤ 6b`, by Cauchy-Schwarz alone.
  have hwide (i : Fin 3) : |inner ℝ (P.basis i) (y - y0)| ≤ 6 * (b : ℝ) :=
    (hspread (P.basis i) (h_cs_bound i 0) (h_cs_bound i 1) (h_cs_bound i 2)).trans
      (by linarith only [hb_one_sub])
  -- Split off the displacement of `y0` from the centre of `P` and add the two bounds.
  have habs {u v A B C : ℝ} (hu : |u| ≤ A) (hv : |v| ≤ B) (h : A + B ≤ C) : |u + v| ≤ C :=
    (abs_add_le u v).trans (by linarith)
  rw [PrismNDim.mem_carrier_iff]
  simp only [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses]
  intro i
  match i with
  | 0 =>
    have hy0 := hy0_P_coord 0
    rw [ht0, NNReal.coe_mul] at hy0
    rw [h_repr_decomp 0, ht0]
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    exact habs hthin hy0 (by linarith only [hθb_nonneg])
  | 1 =>
    have hy0 := hy0_P_coord 1
    rw [ht1] at hy0
    rw [h_repr_decomp 1, ht1]
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    exact habs (hwide 1) hy0 (by linarith only [hb_nonneg, hb_Cang_sub])
  | 2 =>
    have hy0 := hy0_P_coord 2
    rw [ht2, NNReal.coe_one] at hy0
    rw [h_repr_decomp 2, ht2, mul_one]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
    exact habs (hwide 2) hy0 (by linarith only [hb_le_one, hCang_ge_one])

/-- **A grid box meeting a fixed *dilation* of a representative sits in a larger fixed dilation of
it.**  At the constant `4·Cang + 8 + Cc`.

This is what the saturated good cover needs once the shading of a plank is only known to sit in a
fixed dilation `(Pr u)^{(Cc)}` of its representative rather than in `Pr u` itself: the boxes are
then selected by meeting the *dilated* prism, and the undilated version of this lemma does not
apply to them.

This is `Plank.shiftedSlabBox_subset_dilation_core` with its constant relaxed by one through
`Convexity.PrismNDim.dilation_carrier_mono`; the extra unit is not needed by the computation and is
kept only because the callers are stated at `4·Cang + 8 + Cc`. -/
theorem shiftedSlabBox_subset_dilation_of_meet_dilation
    {θ b : ℝ≥0} {hθb : θ * b ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (S : Slab θ hθ1) (t : Fin 3 → ℝ) (q : Fin 3 → ℤ)
    (P : Prism3D (θ * b) b 1 hθb hb1) (Cang Cc : ℝ≥0) (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc)
    (hθ0 : 0 < θ) (hb0 : 0 < b)
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ))
    (hmeet : (((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      ((P.toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty) :
    ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier := by
  exact (shiftedSlabBox_subset_dilation_core S t q P Cang Cc hCang hCc hθ0 hb0 hang hmeet).trans
    (PrismNDim.dilation_carrier_mono P.toPrismNDim (by gcongr; norm_num))

/-! ## The local hypotheses of the dense-box estimate -/

/-- **Hypothesis (3) follows from hypothesis (4).**  A positive local fullness forces the local
family to be nonempty, because `ShadedBody.fullness ∅ Y = 0`.  So the nonemptiness hypothesis of
`Plank.denseBoxEstimate_weighted` is not an independent input. -/
theorem nonempty_of_pos_le_fullness {τ : Type*} (T : Finset τ)
    (Y : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) {lam : ℝ≥0}
    (hlam : 0 < lam) (h : lam ≤ ShadedBody.fullness T Y) : T.Nonempty := by
  refine Finset.nonempty_of_ne_empty fun hT => absurd h (not_le.mpr ?_)
  simpa [hT] using hlam

/-! ## Discharging hypothesis (4) at the box normalisation -/

/-- **Generic Markov / deletion step over a finite family.**  Split a finite family `D` into the
members that clear a `τ`-fraction of their own weight `w` and the rest.  If every discarded member
obeys `m q ≤ τ · w q`, the discarded mass is at most `τ · ∑_{q ∈ D} w q`.  Pure `ENNReal`
bookkeeping; no geometry, no measure theory. -/
theorem markov_mass_split {β : Type*} (D : Finset β) (m w : β → ENNReal) (τ : ENNReal)
    (good : β → Prop) [DecidablePred good]
    (hbad : ∀ q ∈ D, ¬ good q → m q ≤ τ * w q) :
    ∑ q ∈ D, m q ≤ (∑ q ∈ D with good q, m q) + τ * ∑ q ∈ D, w q := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not D good m, Finset.mul_sum]
  refine add_le_add le_rfl ((Finset.sum_le_sum fun q hq => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.filter_subset (fun q => ¬ good q) D)))
  exact hbad q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2

/-- **A plank is tangential to boundedly many boxes of a fixed shift.**  If every box indexed by a
finite set `D` is tangential to the plank `W`, so in particular `a b² ≤ c_tan · |W ∩ B_q|`, then
the fixed-shift overlap bound `Plank.shiftedSlabBox_sum_inter_volume_le` applied to `W` itself
gives

`#D · a b² ≤ 64 · c_tan · a · b`,

that is `#D ≤ 64 c_tan / b`.  This is the quantitative form of "one plank is tangential to `≍ 1/b`
boxes of the grid", the factor that a deletion layer over boxes has to pay for. -/
theorem card_tangentialBoxes_mul_le {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan : ℝ≥0) (S : Slab θ hθ1) (hb : 0 < b) (hθ : 0 < θ) (t : Fin 3 → ℝ)
    (D : Finset (Fin 3 → ℤ)) (W : Plank a b hab hb1)
    (hD : ∀ q ∈ D, Kakeya.ComparableScalars cTan
      (volume ((W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b t q).carrier)).toNNReal (a * b ^ 2)) :
    (D.card : ENNReal) * ((a * b ^ 2 : ℝ≥0) : ENNReal)
      ≤ ((64 * cTan * a * b : ℝ≥0) : ENNReal) := by
  have hvolW : volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((8 * a * b : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier W]; push_cast; ring
  have hWtop : volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ := by
    rw [hvolW]; exact ENNReal.coe_ne_top
  calc (D.card : ENNReal) * ((a * b ^ 2 : ℝ≥0) : ENNReal)
      = ∑ _q ∈ D, ((a * b ^ 2 : ℝ≥0) : ENNReal) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ D, (cTan : ENNReal) * volume ((W.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
          (shiftedSlabBox S b t q).carrier) := Finset.sum_le_sum fun q hq => by
        rw [← ENNReal.coe_toNNReal
            (ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_left)),
          ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        exact (hD q hq).2
    _ ≤ (cTan : ENNReal) * (8 * volume (W.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_right (shiftedSlabBox_sum_inter_volume_le S hb hθ t D
          W.measurableSet_carrier) _
    _ = ((64 * cTan * a * b : ℝ≥0) : ENNReal) := by rw [hvolW]; push_cast; ring

open Classical in
/-- **Total tangential incidence of a whole family.**  Summing
`Plank.card_tangentialBoxes_mul_le` over the planks: with `T_q ⊆ s` the tangential subfamily of the
box `B_q`,

`(∑_{q ∈ D} #T_q) · a b² ≤ 64 · c_tan · a · b · #s`,

so on average a plank is tangential to at most `64 c_tan / b` of the boxes.  Double counting plus
one application of `Plank.card_tangentialBoxes_mul_le` per plank. -/
theorem sum_card_tangential_mul_le {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan : ℝ≥0) (S : Slab θ hθ1) (hb : 0 < b) (hθ : 0 < θ) (t : Fin 3 → ℝ)
    (D : Finset (Fin 3 → ℤ)) (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Tq : (Fin 3 → ℤ) → Finset ι) (hTsub : ∀ q, Tq q ⊆ s)
    (htan : ∀ q, ∀ i ∈ Tq q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b t q).carrier)).toNNReal (a * b ^ 2)) :
    (∑ q ∈ D, ((Tq q).card : ENNReal)) * ((a * b ^ 2 : ℝ≥0) : ENNReal)
      ≤ ((64 * cTan * a * b : ℝ≥0) : ENNReal) * (s.card : ENNReal) := by
  classical
  have hdc : ∑ q ∈ D, (Tq q).card = ∑ i ∈ s, (D.filter (fun q => i ∈ Tq q)).card := by
    have hrw (q) : (Tq q).card = (s.filter (fun i => i ∈ Tq q)).card := by
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hTsub q)]
    simp only [hrw, Finset.card_filter]
    exact Finset.sum_comm
  calc (∑ q ∈ D, ((Tq q).card : ENNReal)) * ((a * b ^ 2 : ℝ≥0) : ENNReal)
      = ∑ i ∈ s, ((D.filter (fun q => i ∈ Tq q)).card : ENNReal)
          * ((a * b ^ 2 : ℝ≥0) : ENNReal) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, ← Nat.cast_sum, hdc]
    _ ≤ ∑ _i ∈ s, ((64 * cTan * a * b : ℝ≥0) : ENNReal) :=
        Finset.sum_le_sum fun i _ => card_tangentialBoxes_mul_le cTan S hb hθ t _ (V i)
          fun q hq => htan q i (Finset.mem_filter.mp hq).2
    _ = ((64 * cTan * a * b : ℝ≥0) : ENNReal) * (s.card : ENNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Plank

end
