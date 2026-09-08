/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap

/-!
# The `θb`-ball grid

This module contains the `θb`-ball grid
`(θb)ℤ³ ∩ 2Q` inside a `θb × b × b` box, its covering and `≤ 27` overlap properties, the associated
measure estimates, and the `DenseBallLayer` record used by the item-1 dense-ball refinement.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

open MeasureTheory
open scoped NNReal

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- A `theta * b` ball, used for the ball grid in item (1) of Lemma 6.13. -/
def thetaBall (theta b : ℝ≥0) (x : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.closedBall x ((theta * b : ℝ≥0) : ℝ)

/-- A finite grid of `theta * b` balls, represented only by its centers.  Covering and overlap
bounds should be separate lemmas/hypotheses. -/
abbrev ThetaBallGrid := Finset (EuclideanSpace ℝ (Fin 3))

/-- Integer multi-indices for the `ℤ³` lattice used in `lem:thetaBallGrid`. -/
abbrev ThetaBallGridIndex := Fin 3 → ℤ

/-- The lattice point with integer coordinates `k` and mesh size `step`, in the coordinates of
`Q`. This is the Lean version of the paper's `step · ℤ³` after rotating/translating by `Q`. -/
def prismLatticePoint {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (Q : Prism3D a b c hab hbc) (step : ℝ≥0) (k : ThetaBallGridIndex) :
    EuclideanSpace ℝ (Fin 3) :=
  Q.center + ∑ i : Fin 3, ((step : ℝ) * (k i : ℝ)) • Q.basis i

/-- The `Q`-coordinates of a lattice point are `step * k`: `basis.repr (latticePoint - center) j
= step * k j`. This is the algebraic heart of the lattice-grid geometry. -/
theorem prismCoord_prismLatticePoint {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (Q : Prism3D a b c hab hbc) (step : ℝ≥0) (k : ThetaBallGridIndex) (j : Fin 3) :
    Q.basis.repr (prismLatticePoint Q step k -ᵥ Q.center) j = (step : ℝ) * (k j : ℝ) := by
  have hv : prismLatticePoint Q step k -ᵥ Q.center
      = ∑ i : Fin 3, ((step : ℝ) * (k i : ℝ)) • Q.basis i := by
    simp only [prismLatticePoint, vsub_eq_sub, add_sub_cancel_left]
  have hortho : ∀ i : Fin 3,
      inner ℝ (Q.basis j) (Q.basis i) = (if j = i then (1 : ℝ) else 0) :=
    fun i => orthonormal_iff_ite.mp Q.basis.orthonormal j i
  rw [Q.basis.repr_apply_apply, hv, inner_sum]
  simp only [real_inner_smul_right, hortho, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- The `2Q` condition for lattice centers, expressed using dilation of the underlying
`PrismNDim`. -/
def memTwoDilate {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (x : EuclideanSpace ℝ (Fin 3)) : Prop :=
  x ∈ (Q.toPrismNDim.dilation (2 : ℝ≥0)).carrier

/-- Membership in `2Q` in coordinates: `x ∈ 2Q ↔ |basis.repr (x - center) i| ≤ 2 · thickness i`. -/
theorem memTwoDilate_iff {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (x : EuclideanSpace ℝ (Fin 3)) :
    memTwoDilate Q x ↔ ∀ i, |Q.basis.repr (x -ᵥ Q.center) i| ≤ 2 * (Q.thicknesses i : ℝ) := by
  rw [memTwoDilate, PrismNDim.mem_carrier_iff]
  simp only [PrismNDim.dilation, PrismNDim.center_mk', PrismNDim.basis_mk',
    PrismNDim.thicknesses_mk', NNReal.coe_mul, NNReal.coe_ofNat]

open scoped Classical in
/-- A finite window of the lattice points with mesh `theta * b`, in the coordinates of `Q`.
The full grid `(theta * b)ℤ³ ∩ 2Q` is obtained by choosing `K` large enough and then filtering
with `memTwoDilate`. The required lower bound on `K` is a small bounding-box lemma. -/
def thetaBallGridWindow {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (K : ℕ) : ThetaBallGrid :=
  ((Finset.Icc (fun _ : Fin 3 => -((K : ℤ))) (fun _ : Fin 3 => (K : ℤ))).filter
      fun k => memTwoDilate Q (prismLatticePoint Q (theta * b) k)).image
    fun k => prismLatticePoint Q (theta * b) k

/-- `𝒞` is exactly the intended lattice grid `(theta * b)ℤ³ ∩ 2Q` in the coordinates of `Q`.
This predicate is intentionally separated from the concrete finite-window implementation above:
the missing geometric work is to prove that some `thetaBallGridWindow Q K` satisfies this
predicate and has the covering/packing properties below. -/
def IsThetaLatticeGrid {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (𝒞 : ThetaBallGrid) : Prop :=
  ∀ x, x ∈ 𝒞 ↔ ∃ k : ThetaBallGridIndex,
    x = prismLatticePoint Q (theta * b) k ∧ memTwoDilate Q x

open scoped Classical in
/-- The complete geometric output of `lem:thetaBallGrid` for one `theta * b × b × b` box:
the centers are `(theta * b)ℤ³ ∩ 2Q`, the associated `theta * b` balls cover `Q`, and any point
belongs to at most `27 = 3³` such balls. -/
def IsThetaBallGridFor {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (𝒞 : ThetaBallGrid) : Prop :=
  IsThetaLatticeGrid Q 𝒞 ∧
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ ⋃ c ∈ 𝒞, thetaBall theta b c ∧
    ∀ x, ({c ∈ 𝒞 | x ∈ thetaBall theta b c}).card ≤ 27

/-- For a large enough window `K`, `thetaBallGridWindow Q K` realizes the intended lattice grid
`(θb)ℤ³ ∩ 2Q` (`IsThetaLatticeGrid`): every lattice point of `2Q` has all its integer coordinates
bounded by some `K` (a bounding-box estimate for the dilated prism). -/
theorem exists_thetaBallGridWindow_isThetaLatticeGrid {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (htheta : 0 < theta) (hb : 0 < b) :
    ∃ K : ℕ, IsThetaLatticeGrid Q (thetaBallGridWindow Q K) := by
  classical
  have hstep0 : (0:ℝ) < ((theta * b : ℝ≥0) : ℝ) := by exact_mod_cast mul_pos htheta hb
  have hthick : ∀ i, (Q.thicknesses i : ℝ) ≤ (b:ℝ) := by
    intro i
    have hle : Q.thicknesses i ≤ b := by
      rw [Q.thicknesses_eq]
      fin_cases i
      · exact mul_le_of_le_one_left hb.le htheta1
      · exact le_rfl
      · exact le_rfl
    exact_mod_cast hle
  refine ⟨⌈2 * (b:ℝ) / ((theta * b : ℝ≥0):ℝ)⌉₊, ?_⟩
  intro x
  simp only [thetaBallGridWindow, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨_, hmem⟩, rfl⟩
    exact ⟨k, rfl, hmem⟩
  · rintro ⟨k, rfl, hmem⟩
    have hbound : ∀ i, |(k i : ℝ)| ≤ (⌈2 * (b:ℝ) / ((theta * b : ℝ≥0):ℝ)⌉₊ : ℝ) := by
      intro i
      have h1 : |((theta * b : ℝ≥0):ℝ) * (k i : ℝ)| ≤ 2 * (Q.thicknesses i : ℝ) := by
        have hm := (memTwoDilate_iff Q _).mp hmem i
        rwa [prismCoord_prismLatticePoint] at hm
      rw [abs_mul, abs_of_nonneg (le_of_lt hstep0)] at h1
      have h3 : ((theta * b : ℝ≥0):ℝ) * |(k i:ℝ)| ≤ 2 * (b:ℝ) :=
        le_trans h1 (by have := hthick i; linarith)
      have h4 : |(k i:ℝ)| ≤ 2 * (b:ℝ) / ((theta * b : ℝ≥0):ℝ) := by
        rw [le_div_iff₀ hstep0, mul_comm]; exact h3
      exact le_trans h4 (Nat.le_ceil _)
    refine ⟨k, ⟨⟨fun i => ?_, fun i => ?_⟩, hmem⟩, rfl⟩
    · have := (abs_le.mp (hbound i)).1; exact_mod_cast this
    · have := (abs_le.mp (hbound i)).2; exact_mod_cast this

/-- The `θb`-lattice grid of `2Q` covers the box `Q`: rounding each `Q`-coordinate of a point of
`Q` to the nearest multiple of `θb` yields a lattice center of `2Q` within distance `θb`. -/
theorem IsThetaLatticeGrid.covers {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    {Q : ThetaBox theta b htheta1} {𝒞 : ThetaBallGrid} (h𝒞 : IsThetaLatticeGrid Q 𝒞)
    (htheta : 0 < theta) (hb : 0 < b) :
    (Q.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ ⋃ c ∈ 𝒞, thetaBall theta b c := by
  intro x hx
  rw [Q.mem_carrier_iff] at hx
  have hstep0 : (0:ℝ) < ((theta * b : ℝ≥0):ℝ) := by exact_mod_cast mul_pos htheta hb
  have hstepthick : ∀ i, ((theta * b : ℝ≥0):ℝ) ≤ (Q.thicknesses i : ℝ) := by
    intro i
    have hle : (theta * b : ℝ≥0) ≤ Q.thicknesses i := by
      rw [Q.thicknesses_eq]; fin_cases i
      · exact le_rfl
      · exact mul_le_of_le_one_left hb.le htheta1
      · exact mul_le_of_le_one_left hb.le htheta1
    exact_mod_cast hle
  set p : ThetaBallGridIndex :=
    fun i => round (Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ)) with hp
  set c : EuclideanSpace ℝ (Fin 3) := prismLatticePoint Q (theta * b) p with hc
  have hdiff : ∀ i, |Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ)|
      ≤ ((theta * b : ℝ≥0):ℝ) / 2 := by
    intro i
    have hround :
        |Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (p i : ℝ)| ≤ 1 / 2 := by
      rw [hp]; exact abs_sub_round _
    have hfac : Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ)
        = ((theta * b : ℝ≥0):ℝ) *
          (Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (p i : ℝ)) := by
      field_simp
    rw [hfac, abs_mul, abs_of_nonneg (le_of_lt hstep0)]
    calc ((theta * b : ℝ≥0):ℝ)
          * |Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (p i : ℝ)|
        ≤ ((theta * b : ℝ≥0):ℝ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hround (le_of_lt hstep0)
      _ = ((theta * b : ℝ≥0):ℝ) / 2 := by ring
  have hmem2 : memTwoDilate Q c := by
    rw [memTwoDilate_iff]
    intro i
    rw [hc, prismCoord_prismLatticePoint]
    have hsplit : |((theta * b : ℝ≥0):ℝ) * (p i : ℝ)|
        ≤ |Q.basis.repr (x -ᵥ Q.center) i|
          + |Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ)| := by
      calc |((theta * b : ℝ≥0):ℝ) * (p i : ℝ)|
          = |Q.basis.repr (x -ᵥ Q.center) i
              - (Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ))| := by
            congr 1; ring
        _ ≤ |Q.basis.repr (x -ᵥ Q.center) i|
              + |Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ)| :=
            abs_sub _ _
    have h2 := hx i
    have h3 : ((theta * b : ℝ≥0):ℝ) / 2 ≤ (Q.thicknesses i : ℝ) := by
      have := hstepthick i; linarith
    have h4 := hdiff i
    linarith
  have hc𝒞 : c ∈ 𝒞 := (h𝒞 c).mpr ⟨p, hc, hmem2⟩
  rw [Set.mem_iUnion₂]
  refine ⟨c, hc𝒞, ?_⟩
  rw [thetaBall, Metric.mem_closedBall, dist_eq_norm]
  have hreprxc : ∀ i, Q.basis.repr (x - c) i
      = Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ) := by
    intro i
    have hsub : (x - c : EuclideanSpace ℝ (Fin 3)) = (x -ᵥ Q.center) - (c -ᵥ Q.center) := by
      simp only [vsub_eq_sub]; abel
    rw [hsub, map_sub, PiLp.sub_apply, hc, prismCoord_prismLatticePoint]
  rw [← Q.basis.repr.norm_map (x - c), EuclideanSpace.norm_eq]
  rw [show ((theta * b : ℝ≥0):ℝ) = Real.sqrt (((theta * b : ℝ≥0):ℝ) ^ 2) from
    (Real.sqrt_sq (le_of_lt hstep0)).symm]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖Q.basis.repr (x - c) i‖ ^ 2
      = ∑ i, |Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ)| ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hreprxc, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin 3, (((theta * b : ℝ≥0):ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := hdiff i
        have hnn := abs_nonneg (Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (p i : ℝ))
        nlinarith [h, hnn, hstep0]
    _ = 3 * (((theta * b : ℝ≥0):ℝ) / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ ((theta * b : ℝ≥0):ℝ) ^ 2 := by nlinarith [hstep0]

/-- A `Q`-coordinate of `u -ᵥ v` is bounded by `dist u v` (orthonormal coordinates are
`1`-Lipschitz projections). -/
theorem abs_repr_vsub_le_dist {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (u v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    |Q.basis.repr (u -ᵥ v) i| ≤ dist u v := by
  rw [Q.basis.repr_apply_apply, dist_eq_norm, ← vsub_eq_sub]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  rw [Q.basis.norm_eq_one i, one_mul]

open scoped Classical in
/-- Bounded overlap of the `θb`-lattice grid: each point lies in at most `27 = 3³` of the balls,
since along each of the three orthonormal axes at most `3` lattice multiples lie within `θb`. -/
theorem IsThetaLatticeGrid.overlap {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    {Q : ThetaBox theta b htheta1} {𝒞 : ThetaBallGrid} (h𝒞 : IsThetaLatticeGrid Q 𝒞)
    (htheta : 0 < theta) (hb : 0 < b) :
    ∀ x, ({c ∈ 𝒞 | x ∈ thetaBall theta b c}).card ≤ 27 := by
  intro x
  have hstep0 : (0:ℝ) < ((theta * b : ℝ≥0):ℝ) := by exact_mod_cast mul_pos htheta hb
  set n : Fin 3 → ℤ :=
    fun i => round (Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ)) with hn
  set idx : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℤ) :=
    fun c i => round (Q.basis.repr (c -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ)) with hidx
  set f : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℤ) := fun c i => idx c i - n i with hf
  set D : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-1 : ℤ) 1) with hD
  -- recovery: on 𝒞, `idx c` is the lattice index `k`, and `c = latticePoint (idx c)`.
  have hrec : ∀ c ∈ 𝒞, (∀ i, Q.basis.repr (c -ᵥ Q.center) i
      = ((theta * b : ℝ≥0):ℝ) * (idx c i : ℝ)) ∧ c = prismLatticePoint Q (theta * b) (idx c) := by
    intro c hc
    obtain ⟨k, rfl, _⟩ := (h𝒞 c).mp hc
    have hk : ∀ i, idx (prismLatticePoint Q (theta * b) k) i = k i := by
      intro i
      simp only [hidx, prismCoord_prismLatticePoint]
      rw [mul_div_cancel_left₀ (k i : ℝ) (ne_of_gt hstep0), round_intCast]
    refine ⟨fun i => ?_, ?_⟩
    · rw [hk i]; exact prismCoord_prismLatticePoint Q (theta * b) k i
    · rw [show idx (prismLatticePoint Q (theta * b) k) = k from funext hk]
  refine le_trans (Finset.card_le_card_of_injOn (t := D) f ?_ ?_) ?_
  · -- maps into D
    intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc
    obtain ⟨hc𝒞, hxc⟩ := hc
    obtain ⟨hcoord, _⟩ := hrec c hc𝒞
    rw [thetaBall, Metric.mem_closedBall] at hxc
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    -- |idx c i - n i| ≤ 1
    have hdc : |Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (idx c i : ℝ)|
        ≤ ((theta * b : ℝ≥0):ℝ) := by
      have h1 : Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (idx c i : ℝ)
          = Q.basis.repr (x -ᵥ c) i := by
        have hsub : (x -ᵥ c : EuclideanSpace ℝ (Fin 3)) = (x -ᵥ Q.center) - (c -ᵥ Q.center) := by
          simp only [vsub_eq_sub]; abel
        rw [hsub, map_sub, PiLp.sub_apply, hcoord i]
      rw [h1]
      exact le_trans (abs_repr_vsub_le_dist Q x c i) hxc
    have hrx : |Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (n i : ℝ)| ≤ 1 / 2 := by
      rw [hn]; exact abs_sub_round _
    have e1 : |(idx c i : ℝ) - Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ)| ≤ 1 := by
      rw [abs_sub_comm]
      have hfac : Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (idx c i : ℝ)
          = (Q.basis.repr (x -ᵥ Q.center) i - ((theta * b : ℝ≥0):ℝ) * (idx c i : ℝ))
            / ((theta * b : ℝ≥0):ℝ) := by field_simp
      rw [hfac, abs_div, abs_of_pos hstep0, div_le_one hstep0]
      exact hdc
    have hkey : |((idx c i : ℝ)) - (n i : ℝ)| ≤ 3 / 2 := by
      calc |((idx c i : ℝ)) - (n i : ℝ)|
          ≤ |(idx c i : ℝ) - Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ)|
            + |Q.basis.repr (x -ᵥ Q.center) i / ((theta * b : ℝ≥0):ℝ) - (n i : ℝ)| :=
            abs_sub_le _ _ _
        _ ≤ 1 + 1 / 2 := add_le_add e1 hrx
        _ = 3 / 2 := by ring
    have hm := abs_le.mp hkey
    have hlt : idx c i - n i < 2 := by
      have hlt' : ((idx c i - n i : ℤ):ℝ) < 2 := by push_cast; linarith [hm.2]
      exact_mod_cast hlt'
    have hgt : (-2 : ℤ) < idx c i - n i := by
      have hgt' : (-2:ℝ) < ((idx c i - n i : ℤ):ℝ) := by push_cast; linarith [hm.1]
      exact_mod_cast hgt'
    simp only [hf]
    exact ⟨by omega, by omega⟩
  · -- injective on the filter set
    intro c hc c' hc' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hc hc'
    obtain ⟨_, hceq⟩ := hrec c hc.1
    obtain ⟨_, hc'eq⟩ := hrec c' hc'.1
    have hidxeq : idx c = idx c' := by
      funext i
      have hthis : idx c i - n i = idx c' i - n i := congrFun heq i
      omega
    rw [hceq, hc'eq, hidxeq]
  · -- card D = 27
    rw [hD, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num [show (Finset.Icc (-1 : ℤ) 1).card = 3 from by decide]

/-- Assembling the three ingredients: some lattice window realizes a full `IsThetaBallGridFor Q`
(exact lattice grid, covering, and `≤ 27` overlap). -/
theorem exists_isThetaBallGridFor {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (htheta : 0 < theta) (hb : 0 < b) :
    ∃ 𝒞 : ThetaBallGrid, IsThetaBallGridFor Q 𝒞 := by
  obtain ⟨K, hK⟩ := exists_thetaBallGridWindow_isThetaLatticeGrid Q htheta hb
  exact ⟨thetaBallGridWindow Q K, hK, hK.covers htheta hb, hK.overlap htheta hb⟩

open scoped Classical in
/-- **Measure consequences of the `θb`-ball grid** (extra6, `lem:thetaBallGrid`, consequences part).
If a `ThetaBallGrid` `𝒞` covers a set `Q` and has bounded overlap `C` (every point lies in at most
`C` of the balls), then `|Q| ≤ ∑_{c ∈ 𝒞} |B(c, θb)| ≤ C · |⋃ balls|`. The lower bound is measure
monotonicity + finite subadditivity; the upper bound is the bounded-overlap union estimate. The
lattice construction producing such a covering grid with an absolute overlap constant is the
separate geometric input `hcover`/`hoverlap`. -/
theorem thetaBallGrid_measure_le {theta b : ℝ≥0}
    (Q : Set (EuclideanSpace ℝ (Fin 3))) (𝒞 : ThetaBallGrid) (C : ℕ)
    (hcover : Q ⊆ ⋃ c ∈ 𝒞, thetaBall theta b c)
    (hoverlap : ∀ x, ({c ∈ 𝒞 | x ∈ thetaBall theta b c}).card ≤ C) :
    volume Q ≤ ∑ c ∈ 𝒞, volume (thetaBall theta b c) ∧
      ∑ c ∈ 𝒞, volume (thetaBall theta b c)
        ≤ (C : ENNReal) * volume (⋃ c ∈ 𝒞, thetaBall theta b c) := by
  refine ⟨?_, ?_⟩
  · calc volume Q
        ≤ volume (⋃ c ∈ 𝒞, thetaBall theta b c) := measure_mono hcover
      _ ≤ ∑ c ∈ 𝒞, volume (thetaBall theta b c) :=
        measure_biUnion_finset_le 𝒞 (fun c => thetaBall theta b c)
  · exact MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le 𝒞
      (fun c _ => measurableSet_closedBall) hoverlap

open scoped Classical in
/-- Once the genuine lattice grid has been constructed, its measure estimate is exactly the
previous bounded-overlap estimate with the constant specialized to `27`. -/
theorem thetaBallGrid_measure_le_27 {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (𝒞 : ThetaBallGrid)
    (h𝒞 : IsThetaBallGridFor Q 𝒞) :
    volume Q.carrier ≤ ∑ c ∈ 𝒞, volume (thetaBall theta b c) ∧
      ∑ c ∈ 𝒞, volume (thetaBall theta b c)
        ≤ (27 : ENNReal) * volume (⋃ c ∈ 𝒞, thetaBall theta b c) :=
  thetaBallGrid_measure_le Q.carrier 𝒞 27 h𝒞.2.1 h𝒞.2.2

open scoped Classical in
/-- **Uncaptured mass is small** (extra6, Step 1 core of `lem:denseBallRefinementGood`).
If a set `V` is covered by the grid `𝒞`, and every ball outside the dense subset `Dset` captures
`< t` of its own measure from `V` (`|V ∩ B(c)| ≤ t · |B(c)|` for `c ∈ 𝒞 \ Dset`), then the part of
`V` missed by the dense balls has measure `≤ t · ∑_{c ∈ 𝒞} |B(c)|`. -/
theorem measure_diff_denseUnion_le {theta b : ℝ≥0}
    (V : Set (EuclideanSpace ℝ (Fin 3))) (𝒞 Dset : ThetaBallGrid) (t : ENNReal)
    (hcover : V ⊆ ⋃ c ∈ 𝒞, thetaBall theta b c)
    (hnondense : ∀ c ∈ 𝒞 \ Dset,
      volume (V ∩ thetaBall theta b c) ≤ t * volume (thetaBall theta b c)) :
    volume (V \ ⋃ c ∈ Dset, thetaBall theta b c)
      ≤ t * ∑ c ∈ 𝒞, volume (thetaBall theta b c) := by
  have hsub : V \ (⋃ c ∈ Dset, thetaBall theta b c)
      ⊆ ⋃ c ∈ 𝒞 \ Dset, (V ∩ thetaBall theta b c) := by
    intro x hx
    obtain ⟨hxV, hxD⟩ := hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcover hxV)
    have hcnotD : c ∉ Dset := fun hcD => hxD (Set.mem_iUnion₂.mpr ⟨c, hcD, hxc⟩)
    exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_sdiff.mpr ⟨hc, hcnotD⟩, hxV, hxc⟩
  calc volume (V \ ⋃ c ∈ Dset, thetaBall theta b c)
      ≤ volume (⋃ c ∈ 𝒞 \ Dset, (V ∩ thetaBall theta b c)) := measure_mono hsub
    _ ≤ ∑ c ∈ 𝒞 \ Dset, volume (V ∩ thetaBall theta b c) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ 𝒞 \ Dset, t * volume (thetaBall theta b c) := Finset.sum_le_sum hnondense
    _ = t * ∑ c ∈ 𝒞 \ Dset, volume (thetaBall theta b c) := by rw [Finset.mul_sum]
    _ ≤ t * ∑ c ∈ 𝒞, volume (thetaBall theta b c) := by
        have hsdiff : 𝒞 \ Dset ⊆ 𝒞 := Finset.sdiff_subset
        gcongr

/-- **Dense-ball layer** for the shading-mass set `V` inside a box `Q`, at density threshold `t`
(extra6, `lem:denseBallRefinementGood`). It bundles the `θb`-ball grid of `Q`, the subset of
*dense* balls (those capturing `≥ t · |B|` of `V`), and the fact that the remaining balls are
*non-dense* (capture `< t · |B|`). This is the record encoding of the dense-ball refinement, so the
downstream statements do not have to unpack `IsThetaBallGridFor` by hand. -/
structure DenseBallLayer {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (V : Set (EuclideanSpace ℝ (Fin 3))) (t : ENNReal) where
  /-- The full `θb`-ball grid covering `Q`. -/
  grid : ThetaBallGrid
  /-- The grid is a genuine lattice grid with covering and `≤ 27` overlap. -/
  grid_ok : IsThetaBallGridFor Q grid
  /-- The mass set `V` sits inside the box. -/
  subset_box : V ⊆ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
  /-- The subset of dense balls. -/
  denseBalls : ThetaBallGrid
  /-- Dense balls are grid balls. -/
  dense_sub : denseBalls ⊆ grid
  /-- Each dense ball captures at least a `t`-fraction of its own measure from `V`. -/
  isDense : ∀ c ∈ denseBalls, t * volume (thetaBall theta b c) ≤ volume (V ∩ thetaBall theta b c)
  /-- Each non-dense grid ball captures less than a `t`-fraction. -/
  nonDense_small : ∀ c ∈ grid \ denseBalls,
    volume (V ∩ thetaBall theta b c) ≤ t * volume (thetaBall theta b c)

/-- **Every mass set inside a box carries a dense-ball layer.**  Take the grid supplied by
`exists_isThetaBallGridFor` and declare a ball dense exactly when it captures at least a
`t`-fraction of its own volume.  The dense/non-dense dichotomy is then the defining property of
`Finset.filter`, so no geometry is involved: the content of a `DenseBallLayer` is entirely in the
grid, which already exists.

This is deliberately stated for an *arbitrary* threshold `t`, since the downstream refinements pick
`t = a ^ (4η)` and the retained-mass estimate is what makes that choice useful, not the split
itself. -/
theorem exists_denseBallLayer {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (htheta : 0 < theta) (hb : 0 < b)
    (V : Set (EuclideanSpace ℝ (Fin 3)))
    (hV : V ⊆ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) (t : ENNReal) :
    Nonempty (DenseBallLayer Q V t) := by
  obtain ⟨𝒞, h𝒞⟩ := exists_isThetaBallGridFor Q htheta hb
  classical
  set D := 𝒞.filter (fun c => t * volume (thetaBall theta b c) ≤ volume (V ∩ thetaBall theta b
      c)) with hD
  refine ⟨{
    grid := 𝒞
    grid_ok := h𝒞
    subset_box := hV
    denseBalls := D
    dense_sub := Finset.filter_subset (fun c => t * volume (thetaBall theta b c) ≤ volume (V ∩
        thetaBall theta b c)) 𝒞
    isDense := by
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    nonDense_small := by
      intro c hc
      rcases Finset.mem_sdiff.mp hc with ⟨hc𝒞, hcD⟩
      have hnot : ¬ (t * volume (thetaBall theta b c) ≤ volume (V ∩ thetaBall theta b c)) := by
        intro h
        apply hcD
        exact Finset.mem_filter.mpr ⟨hc𝒞, h⟩
      exact (not_le.mp hnot).le
  }⟩

/-- **Dropping the non-dense balls loses only a `t · ∑|B|` mass** (Step 1 of
`lem:denseBallRefinementGood`): the part of `V` outside the dense-ball union has measure
`≤ t · ∑_{c ∈ grid} |B(c, θb)|`. Direct from `measure_diff_denseUnion_le` (`V ⊆ Q ⊆ ⋃`). -/
theorem DenseBallLayer.uncaptured_le {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    {Q : ThetaBox theta b htheta1} {V : Set (EuclideanSpace ℝ (Fin 3))} {t : ENNReal}
    (L : DenseBallLayer Q V t) :
    volume (V \ ⋃ c ∈ L.denseBalls, thetaBall theta b c)
      ≤ t * ∑ c ∈ L.grid, volume (thetaBall theta b c) :=
  measure_diff_denseUnion_le V L.grid L.denseBalls t
    (L.subset_box.trans L.grid_ok.2.1) L.nonDense_small

/-- **The dense balls capture almost all the mass**: `|V| ≤ |V ∩ ⋃ dense| + t · ∑_{grid} |B|`.
Combined with `|V| ≥ c·|Q|` and `∑|B| ≤ 27·|⋃|`, small `t` makes the dense balls capture a
`≥ 1/2` fraction of `V` — the good-refinement step of `lem:denseBallRefinementGood`. -/
theorem DenseBallLayer.mass_captured {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    {Q : ThetaBox theta b htheta1} {V : Set (EuclideanSpace ℝ (Fin 3))} {t : ENNReal}
    (L : DenseBallLayer Q V t) :
    volume V ≤ volume (V ∩ ⋃ c ∈ L.denseBalls, thetaBall theta b c)
      + t * ∑ c ∈ L.grid, volume (thetaBall theta b c) := by
  have hmeas : MeasurableSet (⋃ c ∈ L.denseBalls, thetaBall theta b c) :=
    Finset.measurableSet_biUnion _ (fun c _ => measurableSet_closedBall)
  calc volume V
      = volume (V ∩ ⋃ c ∈ L.denseBalls, thetaBall theta b c)
        + volume (V \ ⋃ c ∈ L.denseBalls, thetaBall theta b c) :=
        (measure_inter_add_sdiff V hmeas).symm
    _ ≤ volume (V ∩ ⋃ c ∈ L.denseBalls, thetaBall theta b c)
        + t * ∑ c ∈ L.grid, volume (thetaBall theta b c) := by
        gcongr; exact L.uncaptured_le

/-- The carrier volume of the `3`-dilation of a `3`-dimensional prism is `27 = 3³` times the
original: dilation scales each of the three thicknesses by `3`. -/
theorem volume_dilation_three
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) :
    volume (P.dilation 3).carrier = 27 * volume P.carrier := by
  rw [PrismNDim.volume_carrier (P.dilation 3), PrismNDim.volume_carrier P]
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfinrank]
  simp [PrismNDim.dilation, PrismNDim.thicknesses_mk', Fin.prod_univ_three, ENNReal.coe_mul]
  ring

/-- The union of the `θb`-balls of a lattice grid `𝒞` for `Q` lies in the fixed dilation `3·Q`:
each centre is in `2Q` and each ball has radius `θb ≤ b ≤ Q.thicknesses i`, so a shaded point's
coordinate is `≤ 2·thickness + θb ≤ 3·thickness`. -/
theorem thetaBallGrid_union_subset {theta b : ℝ≥0} {htheta1 : theta ≤ 1}
    (Q : ThetaBox theta b htheta1) (𝒞 : ThetaBallGrid) (h𝒞 : IsThetaBallGridFor Q 𝒞) :
    (⋃ c ∈ 𝒞, thetaBall theta b c) ⊆ (Q.toPrismNDim.dilation 3).carrier := by
  apply Set.iUnion₂_subset
  intro c hc x hx
  have hmem : memTwoDilate Q c := by
    obtain ⟨k, -, hm⟩ := (h𝒞.1 c).mp hc
    exact hm
  rw [memTwoDilate_iff] at hmem
  rw [thetaBall, Metric.mem_closedBall] at hx
  rw [PrismNDim.mem_carrier_iff]
  intro i
  rw [PrismNDim.dilation, PrismNDim.center_mk', PrismNDim.basis_mk', PrismNDim.thicknesses_mk']
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  have hx_sub : x -ᵥ Q.center = (c -ᵥ Q.center) + (x -ᵥ c) := by
    simp only [vsub_eq_sub]; abel
  rw [hx_sub, map_add, PiLp.add_apply]
  have hterm1 : |Q.basis.repr (c -ᵥ Q.center) i| ≤ 2 * (Q.thicknesses i : ℝ) := hmem i
  have hterm2 : |Q.basis.repr (x -ᵥ c) i| ≤ dist x c := abs_repr_vsub_le_dist Q x c i
  have hdist : dist x c ≤ ((theta * b : ℝ≥0) : ℝ) := hx
  have hterm2' : |Q.basis.repr (x -ᵥ c) i| ≤ ((theta * b : ℝ≥0) : ℝ) :=
    le_trans hterm2 hdist
  have hthick : ((theta * b : ℝ≥0) : ℝ) ≤ (Q.thicknesses i : ℝ) := by
    rw [Q.thicknesses_eq]
    fin_cases i
    · rfl
    · have htemp : (theta * b : ℝ≥0) ≤ b := by
        simpa [one_mul] using mul_le_mul_left htheta1 b
      exact mod_cast htemp
    · have htemp : (theta * b : ℝ≥0) ≤ b := by
        simpa [one_mul] using mul_le_mul_left htheta1 b
      exact mod_cast htemp
  calc
    |Q.basis.repr (c -ᵥ Q.center) i + Q.basis.repr (x -ᵥ c) i|
        ≤ |Q.basis.repr (c -ᵥ Q.center) i| + |Q.basis.repr (x -ᵥ c) i| :=
      abs_add_le _ _
    _ ≤ 2 * (Q.thicknesses i : ℝ) + |Q.basis.repr (x -ᵥ c) i| := by
      nlinarith
    _ ≤ 2 * (Q.thicknesses i : ℝ) + ((theta * b : ℝ≥0) : ℝ) := by
      nlinarith
    _ ≤ 3 * (Q.thicknesses i : ℝ) := by
      nlinarith

/-- **Total volume of the `θb`-ball grid** (G4, `lem:geometryThetaBallGridVolume`).  There is an
absolute `Cball > 0` such that for every `θb × b × b` box `Q` and every lattice ball grid `𝒞`
(`IsThetaBallGridFor Q 𝒞`), `∑_{c ∈ 𝒞} |B(c, θb)| ≤ Cball · |Q|`.  The centres lie in `2Q` and
each
ball has radius `θb ≤ b`, so the union of the balls lies in the fixed dilation `3·Q`; combined with
the `27`-overlap sum estimate this gives `Cball = 729`. -/
theorem thetaBallGrid_sum_volume_le :
    ∃ Cball : ℝ≥0, 0 < Cball ∧
      ∀ {theta b : ℝ≥0} {htheta1 : theta ≤ 1} (Q : ThetaBox theta b htheta1),
        0 < theta → 0 < b → ∀ 𝒞 : ThetaBallGrid, IsThetaBallGridFor Q 𝒞 →
          ∑ c ∈ 𝒞, volume (thetaBall theta b c) ≤ (Cball : ENNReal) * volume Q.carrier := by
  refine ⟨729, by norm_num, ?_⟩
  intro theta b htheta1 Q htheta hb 𝒞 h𝒞
  have hsum := (thetaBallGrid_measure_le_27 Q 𝒞 h𝒞).2
  calc ∑ c ∈ 𝒞, volume (thetaBall theta b c)
      ≤ (27:ENNReal) * volume (⋃ c ∈ 𝒞, thetaBall theta b c) := hsum
    _ ≤ (27:ENNReal) * volume (Q.toPrismNDim.dilation 3).carrier := by
      refine mul_le_mul_of_nonneg_left (measure_mono (thetaBallGrid_union_subset Q 𝒞 h𝒞)) ?_
      positivity
    _ = (27:ENNReal) * (27 * volume Q.carrier) := by rw [volume_dilation_three]
    _ = ((729:ℝ≥0):ENNReal) * volume Q.carrier := by
      push_cast
      ring

end Plank

end
