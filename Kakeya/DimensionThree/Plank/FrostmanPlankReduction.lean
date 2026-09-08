/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.SlabAssignmentGeometry
public import Kakeya.DimensionThree.Plank.FrostmanPlankGeometry
public import Kakeya.DimensionThree.Plank.TypedAnchorPrism
public import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Kakeya.DimensionThree.Plank.DenseBox

/-!
# The reduction bridge feeding GWZ Lemma 6.4

This file turns the output of GWZ Lemma 6.13 (`Kakeya.redPlankTube_finalAssembly`, packaged for
Section 6 as `ShadedPlank.reduction_to_slab`) into the ensemble that the Frostman plank estimate
`Kakeya.FrostmanEstimate.plankVolumeLowerBound` consumes, namely
`Kakeya.plankReductionForFrostmanEstimate`.

Three things have to happen on the way, and each is isolated as a named lemma below.

* **Packaging.** 6.13 returns a bare slab map `slabOf`, whereas Section 6 consumes a
  `Plank.SlabAssignment`; that repackaging is `Plank.exists_slabAssignment_of_mem_inSlabFamilyC`
  (in `SlabAssignmentGeometry.lean`). The used-slab set is then the image of the active ensemble
  (`Plank.image_indexSet_slabOf`), which is what makes every used slab carry a nonempty fibre.

* **Geometry of one fibre.** No `Plank.SlabFibreGeometry` is produced anywhere else in the
  development. `Plank.slabFibreGeometry_of_reduction` builds one out of the invariants of a
  `Plank.ThickenedRepr` and a `Plank.SlabAssignment`. Its two genuinely geometric inputs are
  `Plank.thickened_dilation_subset_slab_dilation` (a `cThk`-dilated `θ`-thickening of a plank lying
  in `S^(Cset)` at angle `≤ Cang·θ` still lies in a fixed dilation of `S`) and
  `Plank.thickenedPlank_dilation_subset_closedBall` (a controlled ball for the dilated
  representatives, whose centres are located by `Plank.dist_center_indexSet_le`).

* **Scale bookkeeping.** Every approximate clause of 6.13 carries a factor `a ^ ε` with `ε` chosen
  by the caller, and its analytic constants `cP, c2, c3, …` depend on `η` and `ε`. The Section 6
  interface, by contrast, fixes its constants *before* `η`. The two are reconciled by running 6.13
  at `ε := η` and paying one extra factor of `a ^ η` per clause, which is absorbed at a genuine
  small-scale threshold `b ≤ b₀(η)` via `Kakeya.exists_b₀_nnreal_absorb` and
  `Kakeya.exists_b₀_ennreal_absorb`. This is why the exponents of
  `Kakeya.plankReductionForFrostmanEstimate` are `6 * η`, `2 * η` and `-(3 * η)` rather than the
  `4 * η` and `0` of the paper's `⪆` notation: those losses are real, and hiding them would make
  the statement unprovable from 6.13.

* **Nonconcentration.** `Kakeya.plankReductionForFrostmanEstimate` consumes
  `Plank.IsThickeningNonconcentrated` at the *fixed dilation*
  `Plank.ThickenedRepr.fibreDilation cThk`, not the aligned count of the current public
  `Kakeya.FrostmanEstimate.plankEstimate`. The dilated form is strictly stronger
  (`Plank.IsThickeningNonconcentrated.aligned_card_le`) and the converse is false even for pairwise
  essentially distinct windowed families; the counterexample and the minimal public-statement change
  it forces are recorded in the docstring of `Kakeya.plankReductionForFrostmanEstimate`.

## Post-merge integration of GWZ Lemma 6.4

This integration is **done**. The steps that were carried out were:

1. destructure `Kakeya.plankReductionForFrostmanEstimate` instead of the `NoEtaLoss` variant — the
   constant block is identical, so the `rcases` pattern is unchanged;
2. pass the new nonconcentration hypothesis. `plankVolumeLowerBound` must therefore export the
   dilation factor, i.e. gain a leading `∃ cNC : ℝ≥0, 1 ≤ cNC ∧ …` and replace its aligned count by
   `Plank.IsThickeningNonconcentrated s (ShadedPlank.planks V) cNC M`, with
   `cNC := Plank.ThickenedRepr.fibreDilation cThk` for the `cThk` returned in step 1. The same
   change propagates to `Kakeya.FrostmanEstimate.plankEstimate`, which passes it straight through;
3. feed `Plank.frostmanSlabUnionVolumeLowerBound` the *`η`-loaded* clauses: its per-slab fullness
   hypothesis is `c2 * a ^ (4 * η)` while the reduction now yields `c2 * a ^ (6 * η)`, which is
   stronger for `a ≤ 1` (`NNReal.rpow_le_rpow_of_exponent_ge`), and its Frostman hypothesis takes
   `Cloc * (CF * a ^ (-(3 * η)))` in place of `Cloc * CF`;
4. absorb the two new `η`-losses in `Kakeya.aggregateSlabVolume`'s inputs: the cardinality clause is
   now `Ccard * a ^ (-(3 * η)) * N * |𝒯|` and the slab-sum clause carries `a ^ (2 * η)`. Both are
   fixed powers of `a`, so `Kakeya.expAbsorbConstant` absorbs them into `a ^ ε` after shrinking
   `b₀`, exactly as it already absorbs `c3 / K * Ccard ^ (-β)`. Choosing `η ≤ ε / 16` rather than
   the current `ε / 8` leaves the elementary branch's `a ^ (ε - 2 * η)` margin intact.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Plank

variable {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- A prism contains its own centre: all frame coordinates of the centre vanish, and the
half-widths are nonnegative. -/
theorem prism_center_mem_carrier
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) :
    P.center ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [P.mem_carrier_iff]
  intro k
  simp

/-- **A controlled ball for a dilated representative.** A `θb × b × 1` prism whose centre lies
within `r` of the origin has its `C`-dilation inside the closed ball of radius `r + 3·C`: the three
half-widths of the dilation are `C·θb, C·b, C`, each at most `C`. -/
theorem thickenedPlank_dilation_subset_closedBall {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (Q : ThickenedPlank θ b hθ1 hb1) (C r : ℝ≥0)
    (hQ : dist Q.center (0 : EuclideanSpace ℝ (Fin 3)) ≤ (r : ℝ)) :
    ((Q.toPrismNDim.dilation C).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 ((r : ℝ) + 3 * (C : ℝ)) := by
  intro x hx
  rw [Metric.mem_closedBall]
  have hball := ((Q.toPrismNDim.dilation C).carrier_subset_closedBall) hx
  rw [Metric.mem_closedBall, PrismNDim.dilation_center] at hball
  have hthick : ∀ k : Fin 3,
      (((Q.toPrismNDim.dilation C).thicknesses k : ℝ)) =
        ((C : ℝ) * (((((![(θ * b : ℝ≥0), b, (1 : ℝ≥0)] k) : ℝ≥0) : ℝ)))) := by
    intro k
    simp [PrismNDim.dilation, PrismNDim.thicknesses_mk', Q.thicknesses_eq]
  have hsum : ∑ k : Fin 3, (((Q.toPrismNDim.dilation C).thicknesses k : ℝ))
      ≤ 3 * (C : ℝ) := by
    rw [Fin.sum_univ_three]
    rw [hthick 0, hthick 1, hthick 2]
    simp [Matrix.cons_val_zero]
    have hθ1' : (θ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hθ1
    have hb1' : (b : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hb1
    have hC0 : 0 ≤ (C : ℝ) := by positivity
    have hb0 : 0 ≤ (b : ℝ) := by positivity
    have hθbC : (C : ℝ) * ((θ : ℝ) * (b : ℝ)) ≤ (C : ℝ) * (b : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by simpa using (mul_le_mul_of_nonneg_right hθ1' hb0)) hC0
    have hbC : (C : ℝ) * (b : ℝ) ≤ (C : ℝ) * 1 := by
      exact mul_le_mul_of_nonneg_left hb1' hC0
    linarith
  have htri := dist_triangle x (Q.toPrismNDim.center) (0 : EuclideanSpace ℝ (Fin 3))
  linarith [hball, hsum, htri, hQ]

/-- **Where the active representatives sit.** An active representative `Q ∈ 𝒯` is contained in the
`cThk`-dilation of the thickening of any plank it represents (`ThickenedRepr.repr_subset_thickened`),
so its centre is within `3·cThk` of that plank's centre, which the working window places within
`Plank.windowRadius = 4` of the origin. -/
theorem dist_center_indexSet_le {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk)
    (hwin : IsWindowedFamily s V) {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ R.indexSet) :
    dist Q.center (0 : EuclideanSpace ℝ (Fin 3)) ≤ 4 + 3 * (cThk : ℝ) := by
  classical
  rw [ThickenedRepr.indexSet, Finset.mem_image] at hQ
  rcases hQ with ⟨i, hi, rfl⟩
  -- The centre of the representative lies in its own carrier, and hence in the `cThk`-dilation
  -- of the thickening of the represented plank.
  have hcenterQ : (R.repr i).center ∈ ((R.repr i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa using Plank.prism_center_mem_carrier (R.repr i).toPrismNDim
  have hQT : (R.repr i).center ∈
      ((((V i).thickened θ hθ1).toPrismNDim.dilation cThk).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) :=
    R.repr_subset_thickened i hi hcenterQ
  let T : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    ((V i).thickened θ hθ1).toPrismNDim.dilation cThk
  -- T has the same centre as `(V i)`, and its carrier sits within the ball about that centre of
  -- radius the sum of its (dilated) half-widths.
  have hTcenter : T.center = (V i).center := by
    simp [T]
  have hdistP : dist (R.repr i).center (V i).center ≤ ∑ k : Fin 3, (T.thicknesses k : ℝ) := by
    have hm : (R.repr i).center ∈ Metric.closedBall T.center
        (∑ k : Fin 3, (T.thicknesses k : ℝ)) :=
      T.carrier_subset_closedBall hQT
    have hd : dist (R.repr i).center T.center ≤ ∑ k : Fin 3, (T.thicknesses k : ℝ) :=
      (Metric.mem_closedBall.mp hm)
    rwa [hTcenter] at hd
  -- The working window puts the centre of the represented plank within `windowRadius = 4` of 0.
  have hcenterV : (V i).center ∈ ((V i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa using Plank.prism_center_mem_carrier (V i).toPrismNDim
  have hdistV0 : dist (V i).center (0 : EuclideanSpace ℝ (Fin 3)) ≤ (4 : ℝ) := by
    have hm : (V i).center ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) windowRadius :=
      hwin i hi hcenterV
    have hd : dist (V i).center (0 : EuclideanSpace ℝ (Fin 3)) ≤ windowRadius :=
      (Metric.mem_closedBall.mp hm)
    simpa [windowRadius] using hd
  -- The three half-widths of the dilation are `cThk·θb`, `cThk·b`, `cThk`, each at most `cThk`.
  have hTthick : ∀ k : Fin 3,
      T.thicknesses k = cThk * (![θ * b, b, (1 : NNReal)] k) := by
    intro k
    rw [PrismNDim.dilation_thicknesses]
    rw [((V i).thickened θ hθ1).thicknesses_eq]
  have hle1 : ∀ k : Fin 3, ((![θ * b, b, (1 : NNReal)] k : NNReal) : ℝ) ≤ 1 := by
    intro k
    fin_cases k
    · change (θ : ℝ) * (b : ℝ) ≤ 1
      have hθ0 : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg θ
      have hb0 : 0 ≤ (b : ℝ) := NNReal.coe_nonneg b
      have hθ1' : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
      have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
      nlinarith
    · change (b : ℝ) ≤ 1
      exact_mod_cast hb1
    · change (1 : ℝ) ≤ 1
      norm_num
  have hcomp_le : ∀ k : Fin 3, (T.thicknesses k : ℝ) ≤ (cThk : ℝ) := by
    intro k
    rw [hTthick k]
    rw [NNReal.coe_mul]
    calc
      (cThk : ℝ) * (↑(![θ * b, b, (1 : NNReal)] k) : ℝ) ≤ (cThk : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (hle1 k) (NNReal.coe_nonneg cThk)
      _ = (cThk : ℝ) := by simp
  have hsumT : (∑ k : Fin 3, (T.thicknesses k : ℝ)) ≤ 3 * (cThk : ℝ) := by
    calc
      (∑ k : Fin 3, (T.thicknesses k : ℝ)) ≤ ∑ k : Fin 3, (cThk : ℝ) :=
        Finset.sum_le_sum fun k hk => hcomp_le k
      _ = 3 * (cThk : ℝ) := by simp
  -- Triangle inequality assembles the two bounds.
  calc
    dist (R.repr i).center (0 : EuclideanSpace ℝ (Fin 3))
        ≤ dist (R.repr i).center (V i).center
            + dist (V i).center (0 : EuclideanSpace ℝ (Fin 3)) :=
      dist_triangle _ _ _
    _ ≤ (∑ k : Fin 3, (T.thicknesses k : ℝ)) + 4 := add_le_add hdistP hdistV0
    _ ≤ 3 * (cThk : ℝ) + 4 := by linarith
    _ = 4 + 3 * (cThk : ℝ) := by ring

/-- **A dilated thickening still lies in a controlled dilation of the slab.** If the plank `V` lies
in `S^(Cset)` and makes plane angle at most `Cang·θ` with the `θ × 1 × 1` slab `S`, then the
`cThk`-dilation of its `θ`-thickening lies in `S^(Cset + cThk·(2·Cang + 4))`.

The same statement at the *same* constant `Cset` is false — thickening enlarges the short axis from
`a` to `θb` — which is why the enlarged constant is unavoidable. The proof is the plank template
`Plank.plank_subset_dilation_of_angle_le`, run through the cross-frame coordinate bound
`Plank.abs_inner_slabBasis_le_of_plank_frame_bounds` applied to a rescaled displacement vector, whose
`V`-frame coordinates are supplied by `Plank.abs_inner_dilation_thickened_le`. -/
theorem thickened_dilation_subset_slab_dilation {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (V : Plank a b hab hb1) (S : Slab θ hθ1) (Cang Cset cThk : ℝ≥0)
    (hang : Prism3D.angle V S ≤ (Cang : ℝ) * (θ : ℝ))
    (hVS : (V.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (S.toPrismNDim.dilation Cset).carrier) :
    (((V.thickened θ hθ1).toPrismNDim.dilation cThk).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (S.toPrismNDim.dilation (Cset + cThk * (2 * Cang + 4))).carrier := by
  set W : ThickenedPlank θ b hθ1 hb1 := V.thickened θ hθ1 with hW_def
  -- The angle with `S` is unchanged by thickening (`thickened` preserves the frame).
  have hangW : Prism3D.angle W S ≤ (Cang : ℝ) * (θ : ℝ) := by
    simpa [W] using (Plank.angle_thickened_eq V S).trans_le hang
  intro x hx
  -- The `W`-frame coordinates of `x -ᵥ W.center` are bounded by the `cThk`-dilated thicknesses.
  have hframe : ∀ j : Fin 3,
      |inner ℝ (W.basis j) (x -ᵥ W.center)| ≤ (cThk : ℝ) * ((W.thicknesses j : ℝ≥0) : ℝ) := by
    intro j
    have hj := (PrismNDim.mem_carrier_iff _ x).1 hx j
    rwa [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
      OrthonormalBasis.repr_apply_apply, NNReal.coe_mul] at hj
  by_cases hcThk : cThk = 0
  · -- `cThk = 0`: the `0`-dilation of the thickening is the single point `V.center`.
    subst cThk
    have hframe0 : ∀ i : Fin 3, W.basis.repr (x -ᵥ W.center) i = 0 := by
      intro i
      rw [OrthonormalBasis.repr_apply_apply]
      exact abs_eq_zero.mp (le_antisymm (by simpa using hframe i) (abs_nonneg _))
    have hxW : x -ᵥ W.center = 0 := by
      rw [← W.basis.sum_repr (x -ᵥ W.center)]
      simp only [hframe0]
      simp
    have hWc : W.center = V.center := by simp [W]
    have hxV : x = V.center := (vsub_eq_zero_iff_eq.mp hxW).trans hWc
    have hVc : V.center ∈ ((S.toPrismNDim.dilation Cset).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) :=
      hVS (Plank.prism_center_mem_carrier V.toPrismNDim)
    have hxS : x ∈ ((S.toPrismNDim.dilation Cset).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rwa [hxV]
    exact (PrismNDim.dilation_carrier_mono S.toPrismNDim (by simp)) hxS
  · -- `cThk ≠ 0`: rescale by `sc = 2 / cThk` to make the frame-coordinate bound `2·thickness`.
    have hcThkR : (cThk : ℝ) ≠ 0 := by exact_mod_cast hcThk
    let sc : ℝ := (2 : ℝ) / (cThk : ℝ)
    have hsc_nonneg : 0 ≤ sc := by
      dsimp [sc]
      exact div_nonneg zero_le_two (NNReal.coe_nonneg cThk)
    have hsc_ne : sc ≠ 0 := by
      dsimp [sc]
      exact div_ne_zero (by norm_num) hcThkR
    let w' : EuclideanSpace ℝ (Fin 3) := sc • (x -ᵥ W.center)
    -- The `W`-frame coordinates of `w'` are at most twice the thicknesses.
    have hw' : ∀ j : Fin 3, |inner ℝ (W.basis j) w'| ≤ 2 * ((W.thicknesses j : ℝ≥0) : ℝ) := by
      intro j
      dsimp [w']
      rw [real_inner_smul_right, abs_mul, abs_of_nonneg hsc_nonneg]
      calc
        sc * |inner ℝ (W.basis j) (x -ᵥ W.center)| ≤
            sc * ((cThk : ℝ) * ((W.thicknesses j : ℝ≥0) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hframe j) hsc_nonneg
        _ = 2 * ((W.thicknesses j : ℝ≥0) : ℝ) := by
          dsimp [sc]
          field_simp [hcThkR]
    -- Cross-frame bound in the slab frame.
    have hframeS : ∀ k : Fin 3,
        |inner ℝ (S.basis k) w'| ≤ (4 * (Cang : ℝ) + 8) * ((S.thicknesses k : ℝ≥0) : ℝ) :=
      Plank.abs_inner_slabBasis_le_of_plank_frame_bounds W S Cang le_rfl hangW w' hw'
    -- Undo the rescaling.
    have hsc_inv : sc⁻¹ = (cThk : ℝ) / 2 := by
      dsimp [sc]
      field_simp [hcThkR]
    have hundo : (x -ᵥ W.center) = sc⁻¹ • w' := by
      dsimp [w']
      rw [smul_smul, inv_mul_cancel₀ hsc_ne]
      simp
    have hframeW : ∀ k : Fin 3,
        |inner ℝ (S.basis k) (x -ᵥ W.center)| ≤ (cThk : ℝ) * (2 * (Cang : ℝ) + 4) *
          ((S.thicknesses k : ℝ≥0) : ℝ) := by
      intro k
      rw [hundo, real_inner_smul_right, abs_mul, abs_of_nonneg (inv_nonneg.mpr hsc_nonneg)]
      calc
        sc⁻¹ * |inner ℝ (S.basis k) w'| ≤
            sc⁻¹ * ((4 * (Cang : ℝ) + 8) * ((S.thicknesses k : ℝ≥0) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hframeS k) (inv_nonneg.mpr hsc_nonneg)
        _ = (cThk : ℝ) * (2 * (Cang : ℝ) + 4) * ((S.thicknesses k : ℝ≥0) : ℝ) := by
          rw [hsc_inv]
          ring
    -- The centre of `V` lies in `S^(Cset)`, bounding the offset of the two centres.
    have hVc : V.center ∈ ((S.toPrismNDim.dilation Cset).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) :=
      hVS (Plank.prism_center_mem_carrier V.toPrismNDim)
    have hWc : W.center = V.center := by simp [W]
    have hcenterW : ∀ k : Fin 3,
        |inner ℝ (S.basis k) (W.center -ᵥ S.center)| ≤
          (Cset : ℝ) * ((S.thicknesses k : ℝ≥0) : ℝ) := by
      intro k
      have h := ((S.toPrismNDim.dilation Cset).mem_carrier_iff W.center).mp
        (by simpa [hWc] using hVc) k
      rw [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
        OrthonormalBasis.repr_apply_apply, NNReal.coe_mul] at h
      exact h
    -- Assemble: `x -ᵥ S.center = (x -ᵥ W.center) + (W.center -ᵥ S.center)`.
    refine ((S.toPrismNDim.dilation (Cset + cThk * (2 * Cang + 4))).mem_carrier_iff x).mpr ?_
    intro k
    rw [PrismNDim.dilation_center, PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses,
      OrthonormalBasis.repr_apply_apply, NNReal.coe_mul]
    rw [show x -ᵥ S.center = (x -ᵥ W.center) + (W.center -ᵥ S.center) from
      (vsub_add_vsub_cancel x W.center S.center).symm, inner_add_right]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith only [hframeW k, hcenterW k]

/-- The slabs used by the active ensemble are exactly those used by the family: `𝒮 = 𝒯.image slabOf`
is the image of `s` under `slabOf ∘ repr`, because `𝒯 = s.image repr`. -/
theorem image_indexSet_slabOf {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0} (R : ThickenedRepr s V θ hθ1 cThk)
    (slabOf : ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) :
    R.indexSet.image slabOf = s.image (fun i => slabOf (R.repr i)) := by
  rw [ThickenedRepr.indexSet, Finset.image_image]
  rfl

/-- **The dilated hypothesis implies the aligned one.** A `θ`-thickening sits inside any
`C`-dilation of itself for `1 ≤ C`, so the set counted by `Plank.IsThickeningNonconcentrated` at `C`
contains
the filter of the aligned count. Hence non-concentration in `C`-dilated thickenings is a genuine
strengthening of the aligned hypothesis of `Kakeya.FrostmanEstimate.plankEstimate`.

**The converse is false, and that is the whole content of the interface mismatch**; see the
discussion of `Kakeya.plankReductionForFrostmanEstimate` for an essentially distinct counterexample
in the working window. -/
theorem IsThickeningNonconcentrated.aligned_card_le {s : Finset ι} {V : ι → Plank a b hab hb1}
    {C M : ℝ≥0} (hC : 1 ≤ C) (h : IsThickeningNonconcentrated s V C M)
    (i : ι) (hi : i ∈ s) (φ : ℝ≥0) (hφ1 : φ ≤ 1) (hφa : a / b ≤ φ) :
    ((s.filter fun j => ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        ((V i).thickened φ hφ1).carrier).card : ℝ≥0) ≤ M * φ := by
  classical
  refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (h i hi φ hφ1 hφa)
  refine Finset.monotone_filter_right s fun j _ hj => ?_
  exact hj.trans (PrismNDim.self_subset_dilation ((V i).thickened φ hφ1).toPrismNDim hC)

/-- **Non-concentration passes to subfamilies.** Both the anchor and the counted planks range over
the index set, so shrinking it can only shrink the count. This is the dilated analogue of
`Kakeya.concentration_restrict`, and it is what lets the hypothesis of GWZ Lemma 6.4 — stated for
the original family `s` — be applied to the refinement `s' ⊆ s` that GWZ Lemma 6.13 produces. -/
theorem IsThickeningNonconcentrated.subset {s s' : Finset ι} {V : ι → Plank a b hab hb1}
    {C M : ℝ≥0} (hs' : s' ⊆ s) (h : IsThickeningNonconcentrated s V C M) :
    IsThickeningNonconcentrated s' V C M := by
  classical
  intro i hi φ hφ1 hφa
  refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (h i (hs' hi) φ hφ1 hφa)
  intro j hj
  exact Finset.mem_filter.mpr ⟨hs' (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩

/-- **A uniform upper bound on fibres bounds the total count by the number of fibres.**
`|s| = ∑_{Q ∈ image f} |f⁻¹(Q)| ≤ c · |image f|`. This is the cardinality half of the fibre
comparison that GWZ Lemma 6.13 supplies, in the form GWZ Lemma 6.4 consumes. -/
theorem card_le_mul_card_image_of_fibre_le {κ : Type*} [DecidableEq κ] (t : Finset ι) (f : ι → κ)
    {c : ℝ≥0} (h : ∀ Q ∈ t.image f, ((t.filter fun i => f i = Q).card : ℝ≥0) ≤ c) :
    (t.card : ℝ≥0) ≤ c * ((t.image f).card : ℝ≥0) := by
  classical
  have hsplit : (t.card : ℝ≥0) = ∑ Q ∈ t.image f, ((t.filter fun i => f i = Q).card : ℝ≥0) := by
    rw [← Nat.cast_sum]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ≥0)) (Finset.card_eq_sum_card_image f t)
  calc
    (t.card : ℝ≥0) = ∑ Q ∈ t.image f, ((t.filter fun i => f i = Q).card : ℝ≥0) := hsplit
    _ ≤ ∑ _Q ∈ t.image f, c := Finset.sum_le_sum h
    _ = ((t.image f).card : ℝ≥0) * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = c * ((t.image f).card : ℝ≥0) := mul_comm _ _

/-- **Re-carrying a thickened shading on a larger dilation.** 6.13 delivers a shading whose carrier
is the `Cbox`-dilation of the representative, while `Plank.SlabFibreGeometry` fixes a single loss
constant `Cfib` that must also serve as the controlled-ball radius and the slab-dilation factor.
Intersecting the shade with the larger dilation gives a shading carried by `Q.dilation Cfib` and
leaves the shade unchanged whenever it already sat inside that dilation. -/
theorem exists_dilateShading {θ : ℝ≥0} {hθ1 : θ ≤ 1} (Cfib : ℝ≥0)
    (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∃ Yθ' : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ Q, ((Yθ' Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ Q, (Yθ Q).shade ⊆ ((Q.toPrismNDim.dilation Cfib).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) → (Yθ' Q).shade = (Yθ Q).shade) := by
  refine ⟨fun Q : ThickenedPlank θ b hθ1 hb1 =>
    ({ toConvexSpaceBody := (Q.toPrismNDim.dilation Cfib).toConvexSpaceBody,
       shade := (Yθ Q).shade ∩ ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3))),
       measurableSet_shade := (Yθ Q).measurableSet_shade.inter
         (PrismNDim.measurableSet_carrier (Q.toPrismNDim.dilation Cfib)),
       shade_subset := Set.inter_subset_right } : ShadedBody (EuclideanSpace ℝ (Fin 3))), ?_, ?_⟩
  · intro Q
    rfl
  · intro Q hshade
    change (Yθ Q).shade ∩ ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Yθ Q).shade
    rw [Set.inter_eq_self_of_subset_left hshade]

/-- **The fullness cost of enlarging the shading carriers.** Replacing the `Cbox`-dilation by the
`Cfib`-dilation multiplies every carrier volume by `(Cfib / Cbox) ^ 3` and leaves the shades alone,
so the fullness of the fibre drops by exactly that fixed factor. -/
theorem fullness_dilate {θ : ℝ≥0} {hθ1 : θ ≤ 1} {Cbox Cfib : ℝ≥0}
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hCbox : 0 < Cbox) (hCfib : 0 < Cfib)
    (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
    (Yθ Yθ' : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hshade : ∀ Q ∈ fibre, (Yθ' Q).shade = (Yθ Q).shade)
    (hcar : ∀ Q ∈ fibre, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Q.toPrismNDim.dilation Cbox).carrier)
    (hcar' : ∀ Q ∈ fibre, ((Yθ' Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Q.toPrismNDim.dilation Cfib).carrier) :
    (Cbox ^ 3 / Cfib ^ 3) * ShadedBody.fullness fibre Yθ
      ≤ ShadedBody.fullness fibre Yθ' := by
  set A : ENNReal := (Cbox : ENNReal) ^ 3 with hA
  set B : ENNReal := (Cfib : ENNReal) ^ 3 with hB
  set ρ : ENNReal := B / A with hρ
  have hCboxE : (Cbox : ENNReal) ≠ 0 := by exact_mod_cast hCbox.ne'
  have hCfibE : (Cfib : ENNReal) ≠ 0 := by exact_mod_cast hCfib.ne'
  have hCboxT : (Cbox : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCfibT : (Cfib : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hA0 : A ≠ 0 := by simpa [hA] using pow_ne_zero 3 hCboxE
  have hAf : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.pow_ne_top hCboxT
  have hB0 : B ≠ 0 := by simpa [hB] using pow_ne_zero 3 hCfibE
  have hBf : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.pow_ne_top hCfibT
  -- Every `Yθ' Q`-carrier volume is `ρ` times the corresponding `Yθ Q`-carrier volume:
  -- both are dilations of the same prism, and `(B / A) * (A * v) = B * v` since `A ≠ 0, ⊤`.
  have hcanc (v : ENNReal) : ρ * (A * v) = B * v := by
    calc
      ρ * (A * v) = (B / A) * (A * v) := by rw [hρ]
      _ = (A⁻¹ * B) * (A * v) := by rw [ENNReal.div_eq_inv_mul]
      _ = (A⁻¹ * A) * (B * v) := by ac_rfl
      _ = (1 : ENNReal) * (B * v) := by rw [ENNReal.inv_mul_cancel hA0 hAf]
      _ = B * v := by simp
  have hcarRatio : ∀ Q ∈ fibre, volume (Yθ' Q).carrier = ρ * volume (Yθ Q).carrier := by
    intro Q hQ
    have hdil' : volume ((Q.toPrismNDim.dilation Cfib).carrier) =
        B * volume (Q.toPrismNDim).carrier := by
      simpa [hB] using Plank.volume_dilation (Q.toPrismNDim) Cfib
    have hdil : volume ((Q.toPrismNDim.dilation Cbox).carrier) =
        A * volume (Q.toPrismNDim).carrier := by
      simpa [hA] using Plank.volume_dilation (Q.toPrismNDim) Cbox
    rw [hcar' Q hQ, hcar Q hQ, hdil', hdil]
    exact (hcanc (volume (Q.toPrismNDim).carrier)).symm
  have hshadeCoeff : ∀ Q ∈ fibre, volume (Yθ' Q).shade =
      (1 : ENNReal) * volume (Yθ Q).shade := by
    intro Q hQ
    rw [hshade Q hQ]
    simp
  have hρ0 : ρ ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hB0, hAf⟩
  have hρtop : ρ ≠ ⊤ := ENNReal.div_ne_top hBf hA0
  have hfull' : ShadedBody.fullness' fibre Yθ' =
      (1 / ρ) * ShadedBody.fullness' fibre Yθ :=
    Plank.fullness'_of_scaled fibre Yθ Yθ' 1 ρ hρ0 hρtop hshadeCoeff hcarRatio
  have hρinv : ρ⁻¹ = A / B := by
    rw [hρ]
    exact ENNReal.inv_div (Or.inl hAf) (Or.inl hA0)
  have hfull'' : ShadedBody.fullness' fibre Yθ' =
      (A / B) * ShadedBody.fullness' fibre Yθ := by
    rw [hfull']
    congr 1
    rw [one_div]
    exact hρinv
  -- Descend from `fullness'` (ENNReal) to `fullness` (NNReal).
  have hcoeff : ((Cbox ^ 3 / Cfib ^ 3 : NNReal) : ENNReal) = A / B := by
    rw [ENNReal.coe_div (pow_ne_zero 3 (ne_of_gt hCfib))]
    rw [ENNReal.coe_pow, ENNReal.coe_pow]
  refine ENNReal.coe_le_coe.1 ?_
  rw [ENNReal.coe_mul]
  rw [ShadedBody.coe_fullness]
  rw [hcoeff]
  rw [ShadedBody.coe_fullness]
  rw [hfull'']

/-- **Positive shade mass from a positive fullness bound**, the `mass_pos` field of
`Plank.SlabFibreGeometry`. A fibre of prisms whose fullness is bounded below by `c > 0` carries
positive total shade mass.

No hypothesis on the carriers, on `θ`, on `b` or on nonemptiness of the fibre is needed: fullness is
the `ENNReal` quotient of the total shade mass by the total carrier volume, and `0 / x = 0` for every
`x` (including `0` and `⊤`), so a vanishing numerator forces `fullness = 0 < c`. An earlier version
carried `0 < Cfib`, `0 < θ`, `0 < b`, `fibre.Nonempty` and the carrier identity; all five were unused
(`unusedArguments`), and dropping them lets the lemma be applied before the carrier identity has been
established. -/
theorem mass_pos_of_fullness {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
    (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {c : ℝ≥0} (hc : 0 < c) (hfull : c ≤ ShadedBody.fullness fibre Yθ) :
    0 < ∑ Q ∈ fibre, volume (Yθ Q).shade := by
  by_contra h
  have h_le_zero : (∑ Q ∈ fibre, volume (Yθ Q).shade) ≤ 0 := le_of_not_gt h
  have h_eq_zero : (∑ Q ∈ fibre, volume (Yθ Q).shade) = 0 :=
    le_antisymm h_le_zero zero_le
  have hfull'_zero : ShadedBody.fullness' fibre Yθ = 0 := by
    dsimp [ShadedBody.fullness']
    rw [h_eq_zero]
    exact ENNReal.zero_div
  have hfull_zero : ShadedBody.fullness fibre Yθ = 0 := by
    simp [ShadedBody.fullness, hfull'_zero]
  have hc_pos : (0 : ENNReal) < (c : ℝ≥0) := ENNReal.coe_pos.mpr hc
  have hc_le : ((c : ℝ≥0) : ENNReal) ≤ (ShadedBody.fullness fibre Yθ : ENNReal) :=
    ENNReal.coe_le_coe.mpr hfull
  exact not_le_of_gt hc_pos (by simpa [hfull_zero] using hc_le)

/-- **The slab-fibre geometry of an active fibre.** All seven fields of
`Plank.SlabFibreGeometry` for the fibre of representatives assigned to a used slab `S`, from the
invariants of `R` and `SA` together with the working window and the three numeric requirements on
the loss constant `Cfib`. -/
theorem slabFibreGeometry_of_reduction {s : Finset ι} {V : ι → Plank a b hab hb1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang Cfib : ℝ≥0}
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hcThk : 1 ≤ cThk) (hCfib : 1 ≤ Cfib)
    (R : ThickenedRepr s V θ hθ1 cThk)
    (SA : SlabAssignment s V θ hθ1 R.repr Cset Cang)
    (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hwin : IsWindowedFamily s V)
    (hcar : ∀ Q, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Q.toPrismNDim.dilation Cfib).carrier)
    (hball : 4 + 3 * (cThk : ℝ) + 3 * (Cfib : ℝ) ≤ 4 * (Cfib : ℝ))
    (hslab : Cset + cThk * (2 * Cang + 4) ≤ Cfib)
    (hangC : 2 * Cang + 16 ≤ Cfib)
    (S : Slab θ hθ1)
    (hmass : 0 < ∑ Q ∈ R.indexSet.filter (fun Q => SA.slabOf Q = S), volume (Yθ Q).shade) :
    SlabFibreGeometry (R.indexSet.filter (fun Q => SA.slabOf Q = S)) Yθ S Cfib := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pairwise_essentiallyDistinct
    exact Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) R.indexSet_pairwise
  · -- shade_body
    intro Q _
    exact hcar Q
  · -- subset_controlledBall
    intro Q hQ
    have hQR : Q ∈ R.indexSet := (Finset.mem_filter.mp hQ).1
    have hd : dist Q.center (0 : EuclideanSpace ℝ (Fin 3)) ≤ 4 + 3 * (cThk : ℝ) :=
      Plank.dist_center_indexSet_le R hwin hQR
    have hcast : (((4 + 3 * cThk : ℝ≥0) : ℝ)) = 4 + 3 * (cThk : ℝ) := by
      norm_num [NNReal.coe_add, NNReal.coe_mul]
    have hd' : dist Q.center (0 : EuclideanSpace ℝ (Fin 3)) ≤ ((4 + 3 * cThk : ℝ≥0) : ℝ) := by
      rw [hcast]
      exact hd
    have hD : ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 (4 * (Cfib : ℝ)) := by
      have hD1 : ((Q.toPrismNDim.dilation Cfib).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 (((4 + 3 * cThk : ℝ≥0) : ℝ) + 3 * (Cfib : ℝ)) :=
        Plank.thickenedPlank_dilation_subset_closedBall Q Cfib (4 + 3 * cThk) hd'
      exact hD1.trans (Metric.closedBall_subset_closedBall (by rw [hcast]; linarith [hball]))
    exact hD
  · -- subset_slab
    intro Q hQ
    have hQf := Finset.mem_filter.mp hQ
    have hQR : Q ∈ R.indexSet := hQf.1
    have hEqS : SA.slabOf Q = S := hQf.2
    rcases (Finset.mem_image.mp hQR) with ⟨i, hi, hTi⟩
    have hEq0 : SA.slabOf (R.repr i) = S := by simpa [hTi] using hEqS
    have hmem := Plank.mem_inSlabFamilyC.mp (SA.mem_inSlabFamily i hi)
    have hcarr : (V i).carrier ⊆ ((SA.slabOf (R.repr i)).toPrismNDim.dilation Cset).carrier :=
      hmem.2.1
    have hang : Prism3D.angle (V i) (SA.slabOf (R.repr i)) ≤ (Cang : ℝ) * (θ : ℝ) := hmem.2.2
    have hdil0 : (((V i).thickened θ hθ1).toPrismNDim.dilation cThk).carrier ⊆
        ((SA.slabOf (R.repr i)).toPrismNDim.dilation (Cset + cThk * (2 * Cang + 4))).carrier :=
      Plank.thickened_dilation_subset_slab_dilation (V i) (SA.slabOf (R.repr i))
        Cang Cset cThk hang hcarr
    rw [hEq0] at hdil0
    have hsub : ((R.repr i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (S.toPrismNDim.dilation (Cset + cThk * (2 * Cang + 4))).carrier :=
      (R.repr_subset_thickened i hi).trans hdil0
    rw [← hTi]
    exact hsub.trans (PrismNDim.dilation_carrier_mono S.toPrismNDim hslab)
  · -- thickness_comparable
    intro Q _ i
    rw [Prism3D.thicknesses_eq Q]
    have hCfib_ne : Cfib ≠ 0 := ne_of_gt (zero_lt_one.trans_le hCfib)
    have hCfibi : (Cfib⁻¹ : NNReal) ≤ 1 := by
      rw [NNReal.inv_le hCfib_ne]
      simpa using hCfib
    constructor
    · -- Cfib⁻¹ * u ≤ u
      have hm : Cfib⁻¹ * ![θ * b, b, 1] i ≤ 1 * ![θ * b, b, 1] i :=
        mul_le_mul_of_nonneg_right hCfibi (by positivity : 0 ≤ (![θ * b, b, 1] i : NNReal))
      simpa using hm
    · -- u ≤ Cfib * u
      have hm : 1 * ![θ * b, b, 1] i ≤ Cfib * ![θ * b, b, 1] i :=
        mul_le_mul_of_nonneg_right hCfib (by positivity : 0 ≤ (![θ * b, b, 1] i : NNReal))
      simpa using hm
  · -- tangency
    intro Q hQ j hj
    have hQf := Finset.mem_filter.mp hQ
    have hQR : Q ∈ R.indexSet := hQf.1
    have hEqS : SA.slabOf Q = S := hQf.2
    have hfam : ∀ j' ∈ s, R.repr j' = Q → j' ∈ inSlabFamilyC Cset Cang s V S := by
      intro j' hj' hrepr
      have hmem := SA.mem_inSlabFamily j' hj'
      rwa [hrepr, hEqS] at hmem
    obtain ⟨Pr, hPr_nd, hPr_ang⟩ := Plank.exists_typedAnchorPrism R hθ0 hb0
    have hang' : Prism3D.angle (Pr Q) S ≤ (2 * (Cang : ℝ) + 16) * (θ : ℝ) :=
      hPr_ang Cset Cang S Q hQR hfam
    have hnd : (Pr Q).toPrismNDim = Q.toPrismNDim := hPr_nd Q hQR
    have hb0eq : (Pr Q).basis 0 = Q.basis 0 := by
      simpa using (congrArg (fun P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace ℝ (Fin 3)) => P.basis 0) hnd)
    have hc : 0 ≤ (2 * (Cang : ℝ) + 16) * (θ : ℝ) := by positivity
    have hinner : |inner ℝ ((Pr Q).basis 0) (S.basis j)| ≤ (2 * (Cang : ℝ) + 16) * (θ : ℝ) :=
      Prism3D.abs_inner_basis_zero_le_of_angle_le (Pr Q) S hc hang' hj
    have hCfib_R : 2 * (Cang : ℝ) + 16 ≤ (Cfib : ℝ) := by exact_mod_cast hangC
    have hb : (2 * (Cang : ℝ) + 16) * (θ : ℝ) ≤ (Cfib : ℝ) * (θ : ℝ) := by
      exact mul_le_mul_of_nonneg_right hCfib_R (by positivity)
    exact le_trans (by simpa [hb0eq] using hinner) hb
  · -- mass_pos
    exact hmass

end Plank

namespace Kakeya

/-- **The cross-parent test dilation of Proposition 6.6(A).**

GWZ Lemma 6.4 tests non-concentration against the `C_NC`-dilation of a `θ`-thickened plank
(`Plank.IsThickeningNonconcentrated`), whose transversal half-widths are `C_NC · θ b` and `C_NC · b`.
With `b ≤ 2ρ` the actual factor bodies of the cells inside that container are confined to a region of
transversal radius at most `(2 C_NC + 2) · ρ`, **not** `8 ρ`: the aligned container's `8 ρ` budget
stops being enough as soon as `C_NC > 3`, and `C_NC = (1 + 2 cThk) cThk ≥ 3` always.

`Kakeya.ExternalParentSystem` is *not* generalized for this. Its overlap field is already stated for
test tubes of radius `8 ·` its own scale, and its construction
(`Kakeya.exists_externalParentSystem_of_four_mul_le`) puts no upper bound on that scale — only
`4 δ ≤ scale`. So the parent system is simply instantiated at the enlarged scale
`crossParentTestConst C_NC * ρ`, whose own overlap radius `8 * (crossParentTestConst C_NC * ρ)` then
dominates the confinement radius with room to spare. Nothing in the packing argument changes and the
overlap constant stays the absolute `Kakeya.parentOverlapConst`. -/
def crossParentTestConst (C_NC : ℝ≥0) : ℝ≥0 := 2 * C_NC + 2

theorem one_le_crossParentTestConst (C_NC : ℝ≥0) : 1 ≤ crossParentTestConst C_NC := by
  rw [crossParentTestConst]
  calc (1 : ℝ≥0) ≤ 2 := by norm_num
    _ ≤ 2 * C_NC + 2 := le_add_self

/-- **Absorbing a fixed positive constant into a small scale** (`ℝ≥0` form). For any `c > 0` and any
positive exponent `γ` there is a threshold `b₀ > 0` with `a ^ γ ≤ c` for every `a ≤ b ≤ b₀`.

Take `b₀ = c ^ (1 / γ)`. An earlier version also assumed `0 < a`; it is unused, since at `a = 0` the
conclusion is `0 ^ γ = 0 ≤ c` by `NNReal.zero_rpow` at the positive exponent `γ`. -/
theorem exists_b₀_nnreal_absorb (c : ℝ≥0) (hc : 0 < c) {γ : ℝ} (hγ : 0 < γ) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ ∀ a b : ℝ≥0, a ≤ b → b ≤ b₀ → a ^ γ ≤ c := by
  set b₀ := (c ^ ((1 : ℝ) / γ) : ℝ≥0) with hb₀_def
  have hb₀_pos : 0 < b₀ := by
    dsimp [b₀]
    exact NNReal.rpow_pos hc
  refine ⟨b₀, hb₀_pos, ?_⟩
  intro a b hab hbb₀
  have ha₀ : a ≤ b₀ := le_trans hab hbb₀
  have hγ_nonneg : 0 ≤ γ := le_of_lt hγ
  calc
    a ^ γ ≤ b₀ ^ γ := NNReal.rpow_le_rpow ha₀ hγ_nonneg
    _ = c := by
      dsimp [b₀]
      rw [← NNReal.rpow_mul c ((1 : ℝ) / γ) γ]
      have h_exp : ((1 : ℝ) / γ) * γ = (1 : ℝ) := by
        field_simp [hγ.ne']
      rw [h_exp]
      simp

/-- **Absorbing a fixed positive constant into a small scale** (`ENNReal` form). At `c = ⊤` the
conclusion is trivially true and `b₀ = 1` works; otherwise this is `exists_b₀_nnreal_absorb` at
`c.toNNReal`. As in the `ℝ≥0` form, `0 < a` is not needed. -/
theorem exists_b₀_ennreal_absorb (c : ENNReal) (hc : 0 < c) {γ : ℝ} (hγ : 0 < γ) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ ∀ a b : ℝ≥0, a ≤ b → b ≤ b₀ → (a : ENNReal) ^ γ ≤ c := by
  by_cases hc_top : c = ⊤
  · -- c = ⊤ : any positive `b₀` works, since `(a : ENNReal) ^ γ ≤ ⊤`.
    refine ⟨1, by norm_num, ?_⟩
    intro a b hab hbb₀
    rw [hc_top]
    exact le_top
  · -- c ≠ ⊤ : reduce to the finite part `c.toNNReal`.
    have hc'_pos : 0 < c.toNNReal := ENNReal.toNNReal_pos hc.ne' hc_top
    obtain ⟨b₀, hb₀_pos, hb₀_abs⟩ := exists_b₀_nnreal_absorb c.toNNReal hc'_pos (γ := γ) hγ
    refine ⟨b₀, hb₀_pos, ?_⟩
    intro a b hab hbb₀
    rw [← ENNReal.coe_toNNReal hc_top]
    by_cases ha : a = 0
    · subst a
      simp [ENNReal.zero_rpow_of_pos hγ]
    · rw [← ENNReal.coe_rpow_of_ne_zero ha γ]
      exact ENNReal.coe_le_coe.2 (hb₀_abs a b hab hbb₀)

/-- The Section 6 plank window is the Section 6 working window: both are the ball of radius `4`. -/
theorem isWindowedFamily_of_subset_plankWindow {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → ShadedPlank a b hab hb1)
    (hwin : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) :
    Plank.IsWindowedFamily s (ShadedPlank.planks V) := by
  rw [Plank.IsWindowedFamily]
  intro i hi x hx
  rw [ShadedPlank.planks_carrier] at hx
  simpa [Plank.windowRadius, Kakeya.plankWindowRadius] using hwin i hi hx

/-- **Restricting the plank concentration hypothesis to a subfamily.** -/
theorem concentration_restrict {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s s' : Finset ι} (hs' : s' ⊆ s) (V : ι → ShadedPlank a b hab hb1) {M θ : ℝ≥0}
    (hθ1 : θ ≤ 1)
    (hconc : ∀ i ∈ s, (((s.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
        ((ShadedPlank.planks V i).thickened θ hθ1).carrier)).card : ℕ) : ℝ≥0) ≤ M * θ) :
    ∀ i ∈ s', (((s'.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
        ((ShadedPlank.planks V i).thickened θ hθ1).carrier)).card : ℕ) : ℝ≥0) ≤ M * θ := by
  intro i hi
  have hsub : s'.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
      ((ShadedPlank.planks V i).thickened θ hθ1).carrier) ⊆
      s.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
        ((ShadedPlank.planks V i).thickened θ hθ1).carrier) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨hs' (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
  have hcard : (((s'.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
      ((ShadedPlank.planks V i).thickened θ hθ1).carrier)).card : ℕ) : ℝ≥0) ≤
      (((s.filter (fun j => (ShadedPlank.planks V j).carrier ⊆
        ((ShadedPlank.planks V i).thickened θ hθ1).carrier)).card : ℕ) : ℝ≥0) := by
    exact_mod_cast (Finset.card_le_card hsub)
  exact le_trans hcard (hconc i (hs' hi))

/-- **The Frostman property passes to a heavy subfamily of planks.** All planks of the family have
the same carrier volume `8ab`, so a subfamily retaining a fraction `r` of the cardinality is
Frostman with constant `CF / r`. -/
theorem isFrostmanIn_of_subset_planks {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s s' : Finset ι) (V : ι → ShadedPlank a b hab hb1) (ha : 0 < a) (hb0 : 0 < b)
    (hs' : s' ⊆ s)
    (hwin : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    {CF : ENNReal}
    (hF : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF)
    {r : ℝ≥0} (hr : 0 < r) (hcard : r * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0)) :
    IsFrostmanIn s' (fun i => (V i).toConvexSpaceBody) plankWindow
      (CF * ((r : ENNReal))⁻¹) := by
  have hW : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ plankWindow := by
    intro i hi
    exact hwin i hi
  have hsum (u : Finset ι) :
      (∑ i ∈ u, volume ((V i).toConvexSpaceBody).carrier) =
        (u.card : ENNReal) * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)) := by
    calc
      (∑ i ∈ u, volume ((V i).toConvexSpaceBody).carrier)
          = ∑ _ ∈ u, ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa using ShadedPlank.volume_carrier (V i)
      _ = (u.card : ENNReal) * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_enn : ((r : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal)) := by
    exact_mod_cast hcard
  have hr0 : (r : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hr)
  have hr1 : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hs_le : (s.card : ENNReal) ≤ ((r : ENNReal)⁻¹) * (s'.card : ENNReal) := by
    exact (ENNReal.mul_le_iff_le_inv hr0 hr1).mp hcard_enn
  have hvol : (∑ i ∈ s, volume ((V i).toConvexSpaceBody).carrier)
      ≤ ((r : ENNReal)⁻¹) * (∑ i ∈ s', volume ((V i).toConvexSpaceBody).carrier) := by
    calc
      (∑ i ∈ s, volume ((V i).toConvexSpaceBody).carrier)
          = (s.card : ENNReal) * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)) := hsum s
      _ ≤ ((r : ENNReal)⁻¹) * ((s'.card : ENNReal)
          * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal))) := by
        have hm : (s.card : ENNReal) * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal))
            ≤ ((r : ENNReal)⁻¹ * (s'.card : ENNReal))
                * ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)) := by
          exact mul_le_mul hs_le (le_refl ((8 : ENNReal) * (a : ENNReal) * (b : ENNReal)))
            (by positivity) (by positivity)
        simpa [mul_assoc] using hm
      _ = ((r : ENNReal)⁻¹) * (∑ i ∈ s', volume ((V i).toConvexSpaceBody).carrier) := by
        rw [← hsum s']
  exact IsFrostmanIn.of_le_of_subset (t := s') (C' := ((r : ENNReal)⁻¹)) hF hW hs' hvol

/-- **The reduction bridge feeding GWZ Lemma 6.4.**

From a windowed, pairwise essentially distinct family of `a × b × 1` planks with fullness at least
`a ^ η`, multiplicity at least `a ^ (-η)`, plank concentration `M`, and Frostman constant `CF`, GWZ
Lemma 6.13 produces a refinement `s' ⊆ s`, a typical angle `θ ≥ a / b`, a thickened representative
ensemble `R` with active family `𝒯 = R.indexSet`, a slab assignment `SA`, and a thickened shading
`Yθ`. This lemma packages that output in exactly the shape that
`Kakeya.FrostmanEstimate.plankVolumeLowerBound` consumes: a genuine `Plank.SlabAssignment`, a
`Plank.SlabFibreGeometry` for each used slab, the per-slab fullness, the local Frostman transfer of
`Plank.frostmanThickenedSlabFibre` (whose loss `Cloc` is never rewritten away), and the slab-sum
volume comparison.

## The honest `η`-losses

The geometric constants `cThk, Cset, Cang, Cloc, Cfib, Ccard` and the analytic constants `c2, c3`
are quantified *before* `η`, as the consumer requires. GWZ 6.13, by contrast, quantifies its
analytic constants after `η` and `ε`, and every one of its approximate clauses carries a factor
`a ^ ε`. Running 6.13 at `ε := η` and absorbing both the `a ^ η` and the `η`-dependent constants at
a small-scale threshold `b ≤ b₀(η)` costs one further power of `a ^ η` in each clause. That is the
source of the exponents `6 * η` (fullness, where 6.13 delivers `4 * η + ε`), `2 * η` (slab-sum
volume) and `-(3 * η)` (cardinality, and the Frostman constant, where the loss is the density
`|s| / |s'|` of the refinement). None of these can be removed without a count-based, `ε`-free
version of 6.13.

## The nonconcentration hypothesis is the *dilated* one, and this is a correction

The conclusion `N ≤ Ccard · M · θ` is `Plank.thickenedRepresentativeFibreScale`, whose hypothesis is
`Plank.IsThickeningNonconcentrated s V (Plank.ThickenedRepr.fibreDilation cThk) M`, i.e.
non-concentration inside a **fixed dilation** of the standard `θ`-thickening. This lemma therefore
assumes exactly that, and *not* the aligned count

`|{j ∈ s : P_j ⊆ (P_i)_φ}| ≤ M · φ`

of the current public `Kakeya.FrostmanEstimate.plankEstimate`. The dilated form is strictly stronger
(`Plank.IsThickeningNonconcentrated.aligned_card_le`), and the converse fails **even under the full
hypotheses of GWZ Lemma 6.4** — pairwise essential distinctness, the working window, and the aligned
count at *every* scale `φ ∈ [a/b, 1]` simultaneously.

### An essentially distinct counterexample

Fix a plank `P` with frame `(e₀, e₁, e₂)` and half-widths `(a, b, 1)`, and let
`V = φ · b / (2a)` be an integer (any `φ ∈ [a/b, 1]` with `φ b` small). Define, for
`0 ≤ v < V` and `0 ≤ w < V`, the plank `P_{v,w}` obtained from `P` by

* rolling about the long axis `e₂` by the angle `γ_v = 2 v a / b`;
* translating along `e₀` by `w · a`;
* translating along `e₂` by a *distinct infinitesimal* amount `t_{v,w} ∈ (0, a³)`, injectively.

Then:

* **pairwise essential distinctness holds.** Two members with different rolls differ in roll by at
  least `2a/b`, so the two `a × b` cross-sections meet in area `≲ a²·(b/2a) = ab/2`; two members
  with the same roll differ by at least `a` along the (rolled) thin axis, so their intersection is
  at most half of either. Both cases give `|P ∩ P'| ≤ ½ · max`;
* **the family lies in the working window**: every member is within distance `2` of `P.center`;
* **the aligned count is `1` at every scale.** All members have the *same* long axis `e₂` (rolling
  and translating do not tilt it), so the `e₂`-extent of `P_{v,w}` measured from any other member's
  centre is exactly `1`; the aligned thickening `(P_{v',w'})_φ` also has `e₂`-half-width exactly
  `1`. Containment therefore forces the `e₂`-offset `t_{v,w} - t_{v',w'}` to vanish, which happens
  only for `(v,w) = (v',w')`. So the aligned hypothesis holds with `M = b / a`, which is the least
  admissible value: at `φ = a / b` the count is `1` and `1 ≤ M · (a/b)` forces `M ≥ b/a`;
* **the dilated count is `V² = (φ b / 2a)²` at `C = 3`.** Every member has `e₀`-extent at most
  `a + b γ_{V-1} + (V-1) a ≤ 3 φ b`, `e₁`-extent at most `2 b`, and `e₂`-extent at most `1 + a³`, so
  all `V²` members lie in `((P_{0,0})_φ).dilation 3`.

The ratio `V² / (M φ) = φ b / (4 a)` is unbounded, so **no** constant `M'` depending only on `M` and
the dilation factor can convert the aligned hypothesis into the dilated one. The structural reason:
the aligned thickening widens only the *thin* axis, so it never absorbs a displacement along the two
long axes, while a dilation widens all three. Essential distinctness does not help, because it costs
nothing to place the members at distinct infinitesimal offsets along the long axis.

### The consequence for the public statement

The public `Kakeya.FrostmanEstimate.plankEstimate` and
`Kakeya.FrostmanEstimate.plankVolumeLowerBound` must eventually take the dilated hypothesis. The
minimal change is to export the dilation factor as an extra leading existential and replace the
aligned clause by `Plank.IsThickeningNonconcentrated s (ShadedPlank.planks V) cNC M`; nothing else
in those statements changes, and `cNC` is `Plank.ThickenedRepr.fibreDilation cThk` for the
`cThk` produced here. That edit is deliberately **not** made in this parallel phase, because
`FrostmanPlankEstimate.lean` is owned elsewhere. -/
theorem plankReductionForFrostmanEstimate.{u} :
    ∃ (c2 c3 Ccard cThk Cset Cang Cloc Cfib : ℝ≥0),
      0 < c2 ∧ 0 < c3 ∧ 1 ≤ Ccard ∧ 1 ≤ cThk ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧ 1 ≤ Cloc ∧ 1 ≤ Cfib ∧
      ∀ {η : ℝ}, 0 < η → ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (s : Finset ι) {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
        (hb₀ : b ≤ b₀) (V : ι → ShadedPlank a b hab hb1) (M : ℝ≥0) (CF : ENNReal),
        1 ≤ M → 1 ≤ CF → CF ≠ ⊤ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        a ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (fun i => (V i).toShadedBody) →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D)
          (Plank.ThickenedRepr.fibreDilation cThk) M →
        IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
        ∃ (s' : Finset ι) (N : ℕ) (θ : ℝ≥0) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
          (R : Plank.ThickenedRepr s' (fun i => (V i).toPrism3D) θ hθ1 cThk)
          (SA : Plank.SlabAssignment s' (fun i => (V i).toPrism3D) θ hθ1 R.repr Cset Cang)
          (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))),
          s' ⊆ s ∧ 1 ≤ N ∧ a / b ≤ θ ∧
          (∀ Q ∈ R.indexSet, (Yθ Q).carrier = (Q.toPrismNDim.dilation Cfib).carrier) ∧
          (N : ℝ≥0) ≤ Ccard * M * θ ∧
          (s.card : ℝ≥0) ≤ Ccard * a ^ (-(3 * η)) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) ∧
          (∀ S ∈ SA.used, (R.indexSet.filter (fun Q => SA.slabOf Q = S)).Nonempty) ∧
          (∀ S ∈ SA.used,
            Plank.SlabFibreGeometry (R.indexSet.filter (fun Q => SA.slabOf Q = S)) Yθ S Cfib) ∧
          (∀ S ∈ SA.used, (c2 : ℝ≥0) * a ^ (6 * η) ≤
            ShadedBody.fullness (R.indexSet.filter (fun Q => SA.slabOf Q = S)) Yθ) ∧
          (∀ S ∈ SA.used,
            frostmanConstant (R.indexSet.filter (fun Q => SA.slabOf Q = S))
                (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
              ≤ (Cloc : ENNReal) * (CF * (a : ENNReal) ^ (-(3 * η)))
                * ((R.indexSet.card : ENNReal)
                  / ((R.indexSet.filter (fun Q => SA.slabOf Q = S)).card : ENNReal))
                * volume S.carrier) ∧
          (c3 : ENNReal) * (a : ENNReal) ^ (2 * η) * ∑ S ∈ SA.used,
              volume (⋃ Q ∈ R.indexSet.filter (fun Q => SA.slabOf Q = S), (Yθ Q).shade)
            ≤ volume (⋃ i ∈ s, (V i).shade) := by
  classical
  -- The absolute geometric block of GWZ Lemma 6.13.
  obtain ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkBox, h1Cset, h1Cang, hmain⟩ :=
    Kakeya.plankReduction.{u}
  have h1Cbox : (1 : ℝ≥0) ≤ Cbox := le_trans h1cThk hcThkBox
  -- The local Frostman loss and the fibre-scale constant, both `η`-independent.
  obtain ⟨Cloc, h1Cloc, hloc⟩ :=
    Plank.frostmanThickenedSlabFibre.{u} cThk Cset Cang cN h1cThk h1Cset h1Cang h1cN
  obtain ⟨Ccard₀, h1Ccard₀, hscale⟩ :=
    Plank.thickenedRepresentativeFibreScale.{u} cThk cN h1cThk h1cN
  -- The slab-fibre loss constant: large enough for all three numeric requirements of
  -- `Plank.slabFibreGeometry_of_reduction`, and at least `Cbox`.
  set Cfib : ℝ≥0 := (4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4)) + (2 * Cang + 16) + Cbox
    with hCfib_def
  have hCfibA : 4 + 3 * cThk ≤ Cfib := by
    rw [hCfib_def]
    calc 4 + 3 * cThk ≤ (4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4)) := le_self_add
      _ ≤ ((4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4))) + (2 * Cang + 16) := le_self_add
      _ ≤ _ := le_self_add
  have hCfibB : Cset + cThk * (2 * Cang + 4) ≤ Cfib := by
    rw [hCfib_def]
    calc Cset + cThk * (2 * Cang + 4)
        ≤ (4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4)) := le_add_self
      _ ≤ ((4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4))) + (2 * Cang + 16) := le_self_add
      _ ≤ _ := le_self_add
  have hCfibC : 2 * Cang + 16 ≤ Cfib := by
    rw [hCfib_def]
    calc 2 * Cang + 16
        ≤ ((4 + 3 * cThk) + (Cset + cThk * (2 * Cang + 4))) + (2 * Cang + 16) := le_add_self
      _ ≤ _ := le_self_add
  have hCboxCfib : Cbox ≤ Cfib := by rw [hCfib_def]; exact le_add_self
  have hCfib1 : (1 : ℝ≥0) ≤ Cfib := le_trans h1Cbox hCboxCfib
  have hCfib0 : (0 : ℝ≥0) < Cfib := lt_of_lt_of_le zero_lt_one hCfib1
  have hCbox0 : (0 : ℝ≥0) < Cbox := lt_of_lt_of_le zero_lt_one h1Cbox
  -- The fixed fullness loss of re-carrying the shading on the larger dilation.
  set ρ : ℝ≥0 := Cbox ^ 3 / Cfib ^ 3 with hρ_def
  have hρ0 : (0 : ℝ≥0) < ρ := by
    rw [hρ_def]
    exact div_pos (pow_pos hCbox0 3) (pow_pos hCfib0 3)
  refine ⟨1, 1, Ccard₀ + cN, cThk, Cset, Cang, Cloc, Cfib, one_pos, one_pos,
    le_trans h1Ccard₀ le_self_add, h1cThk, h1Cset, h1Cang, h1Cloc, hCfib1, ?_⟩
  intro η hη
  obtain ⟨cP, cLam, c1, c2₆, c3₆, c4, hcP, hcLam, hc1, hc2₆, hc3₆, hc4, hcfg⟩ := hmain hη hη
  -- The three constant absorptions, and the small-scale bound giving `a < 1`.
  obtain ⟨b₁, hb₁, habs₁⟩ := Kakeya.exists_b₀_nnreal_absorb (ρ * c2₆) (mul_pos hρ0 hc2₆) hη
  obtain ⟨b₂, hb₂, habs₂⟩ := Kakeya.exists_b₀_nnreal_absorb cP hcP hη
  obtain ⟨b₃, hb₃, habs₃⟩ := Kakeya.exists_b₀_nnreal_absorb c3₆ hc3₆ hη
  refine ⟨min (1 / 2) (min b₁ (min b₂ b₃)), ?_, ?_⟩
  · exact lt_min (by norm_num) (lt_min hb₁ (lt_min hb₂ hb₃))
  intro ι s a b ha hab hb1 hb₀ V M CF hM hCF1 hCFtop hwin hED hfull hmult hNC hFrost
  -- Small-scale consequences of the threshold.
  have hb_half : b ≤ 1 / 2 := hb₀.trans (min_le_left _ _)
  have hbb₁ : b ≤ b₁ := hb₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbb₂ : b ≤ b₂ :=
    hb₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbb₃ : b ≤ b₃ :=
    hb₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hA₁ : a ^ η ≤ ρ * c2₆ := habs₁ a b hab hbb₁
  have hA₂ : a ^ η ≤ cP := habs₂ a b hab hbb₂
  have hA₃ : a ^ η ≤ c3₆ := habs₃ a b hab hbb₃
  have hb0 : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have ha1 : a < 1 := lt_of_le_of_lt (hab.trans hb_half) (by norm_num)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hapow : (0 : ℝ≥0) < a ^ η := NNReal.rpow_pos ha
  have hwinF : Plank.IsWindowedFamily s (fun i => (V i).toPrism3D) :=
    Kakeya.isWindowedFamily_of_subset_plankWindow s V hwin
  -- The family is nonempty: the multiplicity threshold is positive.
  have hs_ne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exfalso
      rw [ShadedBody.multiplicity_empty] at hmult
      have hpos : (0 : ENNReal) < (a : ENNReal) ^ (-η) :=
        ENNReal.rpow_pos (by exact_mod_cast ha) ENNReal.coe_ne_top
      exact hpos.ne' (le_antisymm hmult hpos.le)
    · exact h
  have hscard_pos : (0 : ℝ≥0) < (s.card : ℝ≥0) := by
    exact_mod_cast Finset.card_pos.mpr hs_ne
  -- GWZ Lemma 6.13, run at `ε := η`.
  obtain ⟨s', Y', N, θ, hθ1, R, slabOf, Yθ, hrefine, hcards, _hlams, hN1, hθa, hslabmem,
    hcarbox, hfib2, _hitem1, hitem2, hitem3, _hitem4⟩ := hcfg s V ha ha1 hwinF hED hfull hmult
  have hs's : s' ⊆ s := hrefine.1
  have hθ0 : (0 : ℝ≥0) < θ := lt_of_lt_of_le (div_pos ha hb0) hθa
  -- The refinement is nonempty, hence so is the active ensemble.
  have hr0 : (0 : ℝ≥0) < cP * a ^ η * a ^ η := mul_pos (mul_pos hcP hapow) hapow
  have hs'card_pos : (0 : ℝ≥0) < (s'.card : ℝ≥0) :=
    lt_of_lt_of_le (mul_pos hr0 hscard_pos) hcards
  have hs'_ne : s'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hs'card_pos)
  have hTne : R.indexSet.Nonempty :=
    ⟨R.repr hs'_ne.choose, R.repr_mem_indexSet hs'_ne.choose_spec⟩
  have hwinF' : Plank.IsWindowedFamily s' (fun i => (V i).toPrism3D) :=
    fun i hi => hwinF i (hs's hi)
  have hNC' : Plank.IsThickeningNonconcentrated s' (fun i => (V i).toPrism3D)
      (Plank.ThickenedRepr.fibreDilation cThk) M :=
    Plank.IsThickeningNonconcentrated.subset hs's hNC
  -- Re-carry the shading on the `Cfib`-dilation.
  obtain ⟨Yθ', hcarfib, hshade_eq⟩ := Plank.exists_dilateShading (b := b) (hb1 := hb1) Cfib Yθ
  have hshadeQ : ∀ Q ∈ R.indexSet, (Yθ' Q).shade = (Yθ Q).shade := by
    intro Q hQ
    refine hshade_eq Q (((Yθ Q).shade_subset).trans ?_)
    rw [hcarbox Q hQ]
    exact PrismNDim.dilation_carrier_mono Q.toPrismNDim hCboxCfib
  -- The three numeric requirements of `Plank.slabFibreGeometry_of_reduction`.
  have hballR : 4 + 3 * (cThk : ℝ) + 3 * (Cfib : ℝ) ≤ 4 * (Cfib : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hCfibA
    push_cast at h
    linarith
  -- Nonemptiness of each active slab fibre.
  have hfibne : ∀ S ∈ R.indexSet.image slabOf,
      (R.indexSet.filter (fun Q => slabOf Q = S)).Nonempty := by
    intro S hS
    obtain ⟨Q, hQ, hQS⟩ := Finset.mem_image.mp hS
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, hQS⟩⟩
  -- Per-slab fullness, after the carrier enlargement.
  have hfullS : ∀ S ∈ R.indexSet.image slabOf,
      (1 : ℝ≥0) * a ^ (6 * η)
        ≤ ShadedBody.fullness (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ' := by
    intro S hS
    have h613 := (hitem2 S hS).1
    have hdil := Plank.fullness_dilate hθ0 hb0 hCbox0 hCfib0
      (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ Yθ'
      (fun Q hQ => hshadeQ Q (Finset.mem_filter.mp hQ).1)
      (fun Q hQ => hcarbox Q (Finset.mem_filter.mp hQ).1) (fun Q _ => hcarfib Q)
    have hsplit : a ^ (6 * η) = a ^ η * (a ^ (4 * η) * a ^ η) := by
      rw [← NNReal.rpow_add ha_ne, ← NNReal.rpow_add ha_ne]
      ring_nf
    calc (1 : ℝ≥0) * a ^ (6 * η) = a ^ η * (a ^ (4 * η) * a ^ η) := by rw [one_mul, hsplit]
      _ ≤ (ρ * c2₆) * (a ^ (4 * η) * a ^ η) := by gcongr
      _ = ρ * (c2₆ * a ^ (4 * η) * a ^ η) := by ring
      _ ≤ ρ * ShadedBody.fullness (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ := by gcongr
      _ ≤ _ := hdil
  have hmassS : ∀ S ∈ R.indexSet.image slabOf,
      0 < ∑ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), volume (Yθ' Q).shade := by
    intro S hS
    exact Plank.mass_pos_of_fullness _ Yθ' (by positivity) (hfullS S hS)
  -- The slab-fibre geometry of each active fibre.
  have hgeoS : ∀ S ∈ R.indexSet.image slabOf,
      Plank.SlabFibreGeometry (R.indexSet.filter (fun Q => slabOf Q = S)) Yθ' S Cfib := by
    intro S hS
    exact Plank.slabFibreGeometry_of_reduction hθ0 hb0 h1cThk hCfib1 R
      ⟨slabOf, R.indexSet.image slabOf,
        fun i hi => Finset.mem_image_of_mem slabOf (R.repr_mem_indexSet hi), hslabmem⟩
      Yθ' hwinF' (fun Q => hcarfib Q) hballR hCfibB hCfibC S (hmassS S hS)
  -- The fibre scale.
  have hfiblo : ∀ Q ∈ R.indexSet,
      (N : ℝ) / (cN : ℝ) ≤ ((s'.filter fun i => R.repr i = Q).card : ℝ) :=
    fun Q hQ => (hfib2 Q hQ).1
  have hNle : (N : ℝ≥0) ≤ (Ccard₀ + cN) * M * θ := by
    refine le_trans
      (hscale s' (fun i => (V i).toPrism3D) θ hθ1 R M N hθ0 hθa hM hNC' hTne hfiblo) ?_
    gcongr
    exact le_self_add
  -- The cardinality comparison.
  have hfibhi : ∀ Q ∈ R.indexSet,
      ((s'.filter fun i => R.repr i = Q).card : ℝ≥0) ≤ cN * (N : ℝ≥0) := by
    intro Q hQ
    exact_mod_cast (hfib2 Q hQ).2
  have hs'le : (s'.card : ℝ≥0) ≤ cN * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) :=
    Plank.card_le_mul_card_image_of_fibre_le s' R.repr hfibhi
  have hcard3 : a ^ (3 * η) * (s.card : ℝ≥0)
      ≤ (Ccard₀ + cN) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := by
    have hsplit : a ^ (3 * η) = a ^ η * (a ^ η * a ^ η) := by
      rw [← NNReal.rpow_add ha_ne, ← NNReal.rpow_add ha_ne]
      ring_nf
    calc a ^ (3 * η) * (s.card : ℝ≥0) = a ^ η * (a ^ η * a ^ η) * (s.card : ℝ≥0) := by rw [hsplit]
      _ ≤ cP * (a ^ η * a ^ η) * (s.card : ℝ≥0) := by gcongr
      _ = cP * a ^ η * a ^ η * (s.card : ℝ≥0) := by ring
      _ ≤ (s'.card : ℝ≥0) := hcards
      _ ≤ cN * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := hs'le
      _ ≤ (Ccard₀ + cN) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := by gcongr; exact le_add_self
  have hcardFinal : (s.card : ℝ≥0)
      ≤ (Ccard₀ + cN) * a ^ (-(3 * η)) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := by
    have hinv : a ^ (-(3 * η)) * a ^ (3 * η) = 1 := by
      rw [← NNReal.rpow_add ha_ne]
      simp
    calc (s.card : ℝ≥0) = a ^ (-(3 * η)) * (a ^ (3 * η) * (s.card : ℝ≥0)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ a ^ (-(3 * η)) * ((Ccard₀ + cN) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0)) := by gcongr
      _ = (Ccard₀ + cN) * a ^ (-(3 * η)) * (N : ℝ≥0) * (R.indexSet.card : ℝ≥0) := by ring
  -- The local Frostman transfer.
  have hVwin' : ∀ i ∈ s', ((V i).toPrism3D).toConvexSpaceBody ≤ plankWindow := by
    intro i hi
    exact hwin i (hs's hi)
  have hFrost' : IsFrostmanIn s' (fun i => (V i).toConvexSpaceBody) plankWindow
      (CF * ((cP * a ^ η * a ^ η : ℝ≥0) : ENNReal)⁻¹) :=
    Kakeya.isFrostmanIn_of_subset_planks s s' V ha hb0 hs's hwin hFrost hr0 hcards
  have hrle : (a : ENNReal) ^ (3 * η) ≤ ((cP * a ^ η * a ^ η : ℝ≥0) : ENNReal) := by
    have hnn : a ^ (3 * η) ≤ cP * a ^ η * a ^ η := by
      have hsplit : a ^ (3 * η) = a ^ η * a ^ η * a ^ η := by
        rw [← NNReal.rpow_add ha_ne, ← NNReal.rpow_add ha_ne]
        ring_nf
      rw [hsplit]
      gcongr
    calc (a : ENNReal) ^ (3 * η) = ((a ^ (3 * η) : ℝ≥0) : ENNReal) :=
          (ENNReal.coe_rpow_of_ne_zero ha_ne _).symm
      _ ≤ _ := ENNReal.coe_le_coe.mpr hnn
  have hinvle : ((cP * a ^ η * a ^ η : ℝ≥0) : ENNReal)⁻¹ ≤ (a : ENNReal) ^ (-(3 * η)) := by
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr hrle
  have hfr := hloc s' (fun i => (V i).toPrism3D) θ hθ1 R
    ⟨slabOf, R.indexSet.image slabOf,
      fun i hi => Finset.mem_image_of_mem slabOf (R.repr_mem_indexSet hi), hslabmem⟩
    N (CF * ((cP * a ^ η * a ^ η : ℝ≥0) : ENNReal)⁻¹) ha hθ0 hN1 hfib2 hVwin' hFrost'
  have hfrostS : ∀ S ∈ R.indexSet.image slabOf,
      frostmanConstant (R.indexSet.filter (fun Q => slabOf Q = S))
          (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
        ≤ (Cloc : ENNReal) * (CF * (a : ENNReal) ^ (-(3 * η)))
          * ((R.indexSet.card : ENNReal)
            / ((R.indexSet.filter (fun Q => slabOf Q = S)).card : ENNReal))
          * volume S.carrier := by
    intro S hS
    refine le_trans (hfr S hS (hfibne S hS)) ?_
    gcongr
  -- The slab-sum volume comparison.
  have hsum_eq : ∑ S ∈ R.indexSet.image slabOf,
        volume (⋃ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), (Yθ' Q).shade)
      = ∑ S ∈ R.indexSet.image slabOf,
        volume (⋃ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), (Yθ Q).shade) := by
    refine Finset.sum_congr rfl fun S _ => congrArg volume ?_
    exact Set.iUnion₂_congr fun Q hQ => hshadeQ Q (Finset.mem_filter.mp hQ).1
  have hcoef : (1 : ENNReal) * (a : ENNReal) ^ (2 * η) ≤ ((c3₆ * a ^ η : ℝ≥0) : ENNReal) := by
    have hnn : a ^ (2 * η) ≤ c3₆ * a ^ η := by
      have hsplit : a ^ (2 * η) = a ^ η * a ^ η := by
        rw [← NNReal.rpow_add ha_ne]
        ring_nf
      rw [hsplit]
      gcongr
    calc (1 : ENNReal) * (a : ENNReal) ^ (2 * η) = ((a ^ (2 * η) : ℝ≥0) : ENNReal) := by
          rw [one_mul, ENNReal.coe_rpow_of_ne_zero ha_ne]
      _ ≤ _ := ENNReal.coe_le_coe.mpr hnn
  have hsumFinal : (1 : ENNReal) * (a : ENNReal) ^ (2 * η) * ∑ S ∈ R.indexSet.image slabOf,
        volume (⋃ Q ∈ R.indexSet.filter (fun Q => slabOf Q = S), (Yθ' Q).shade)
      ≤ volume (⋃ i ∈ s, (V i).shade) := by
    rw [hsum_eq]
    exact le_trans (mul_le_mul_right' hcoef _) hitem3
  exact ⟨s', N, θ, hθ0, hθ1, R,
    ⟨slabOf, R.indexSet.image slabOf,
      fun i hi => Finset.mem_image_of_mem slabOf (R.repr_mem_indexSet hi), hslabmem⟩,
    Yθ', hs's, hN1, hθa, fun Q _ => hcarfib Q, hNle, hcardFinal, hfibne, hgeoS, hfullS, hfrostS,
    hsumFinal⟩

end Kakeya

end

end
